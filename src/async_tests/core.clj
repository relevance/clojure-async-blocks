(ns async-tests.core
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [clojure.tools.namespace.repl :refer [refresh]]
            [no.disassemble :refer [disassemble]]))


;; State monad stuff, used only in SSA construction

(defn- with-bind [id expr psym body]
  `(fn [~psym]
     (let [[~id ~psym] ( ~expr ~psym)]
       (assert ~psym "Nill plan")
       ~body)))

(defmacro gen-plan [binds id-expr]
  (let [binds (partition 2 binds)
        psym (gensym "plan_")
        f (reduce
           (fn [acc [id expr]]
             `(~(with-bind id expr psym acc)
               ~psym))
           `[~id-expr ~psym]
           (reverse binds))]
    `(fn [~psym]
       ~f)))

(defn get-plan [f]
  (f {}))

(defn push-binding [key value]
  (fn [plan]
    [nil (update-in plan [:bindings key] conj value)]))

(defn push-alter-binding [key f & args]
  (println "args---->  " args)
  (fn [plan]
    [nil (update-in plan [:bindings key]
                  #(conj % (apply f (first %) args)))]))

(defn get-binding [key]
  (fn [plan]
    [(first (get-in plan [:bindings key])) plan]))

(defn pop-binding [key]
  (fn [plan]
    [(first (get-in plan [:bindings key]))
     (update-in plan [:bindings key] pop)]))

(defn no-op []
  (fn [plan]
    [nil plan]))

(defn all [itms]
  (fn [plan]
    (reduce
     (fn [[ids plan] f]
       (let [[id plan] (f plan)]
         [(conj ids id) plan]))
     [[] plan]
     itms)))

(defn assoc-in-plan [path val]
  (fn [plan]
    [val (assoc-in plan path val)]))

(defn update-in-plan [path f & args]
  (fn [plan]
    [nil (apply update-in plan path f args)]))

(defn get-in-plan [path]
  (fn [plan]
    [(get-in plan path) plan]))


(defn set-block [block-id]
  (fn [plan]
    [block-id (assoc plan :current-block block-id)]))

(defn get-block []
  (fn [plan]
    [(:current-block plan) plan]))

(defn add-block []
  (let [blk-sym (keyword (gensym "blk_"))]
    (gen-plan
     [cur-blk (get-block)
      _ (assoc-in-plan [:blocks blk-sym] [])
      _ (if-not cur-blk
          (assoc-in-plan [:start-block] blk-sym)
          (no-op))]
     blk-sym)))

(defn add-instruction [inst]
  (pprint inst)
  (let [inst-id (gensym "inst_")
        inst (assoc inst :id inst-id)]
    (gen-plan
     [blk-id (get-block)
      _ (update-in-plan [:blocks blk-id] (fnil conj []) inst)]
     inst-id)))

;;

;; We're going to reduce Clojure expressions to a "bytecode" format,
;; and then translate those bytecodes back into Clojure data. Here we
;; define the bytecodes:

(defprotocol IInstruction
  (instruction-references [this] "Returns all the instruction ids referenced by this instruction")
  (block-references [this] "Returns all the blocks this instruction references")
  (emit-instruction [this state-sym] "Returns the clojure code that this instruction represents"))

(defrecord Const [value]
  IInstruction
  (instruction-references [this] [])
  (block-references [this] [])
  (emit-instruction [this state-sym]
    (if (= value ::value)
      `[~(:id this) (::value ~state-sym)]
      `[~(:id this) ~value])))

(defrecord Set [id value]
  IInstruction
  (instruction-references [this] [value])
  (block-references [this] [])
  (emit-instruction [this state-sym]
    `[~id ~value]))

(defrecord Call [refs]
  IInstruction
  (instruction-references [this] refs)
  (block-references [this] [])
  (emit-instruction [this state-sym]
    `[~(:id this) ~(seq refs)]))

(defrecord Jmp [value block]
  IInstruction
  (instruction-references [this] [value])
  (block-references [this] [block])
  (emit-instruction [this state-sym]
    `(recur (assoc ~state-sym ::value ~value ::state ~block))))

(defrecord Return [value]
  IInstruction
  (instruction-references [this] [value])
  (block-references [this] [])
  (emit-instruction [this state-sym]
    `(assoc ~state-sym ::value ~value ::state ::finished)))

(defrecord Await [value block]
  IInstruction
  (instruction-references [this] [value])
  (block-references [this] [block])
  (emit-instruction [this state-sym]
    `(assoc ~state-sym ::value ~value ::state ~block)))

(defrecord CondBr [test then-block else-block]
  IInstruction
  (instruction-references [this] [test])
  (block-references [this] [then-block else-block])
  (emit-instruction [this state-sym]
    `(if ~test
       (recur (assoc ~state-sym ::state ~then-block))
       (recur (assoc ~state-sym ::state ~else-block)))))




(defn debug [x]
  (pprint x)
  x)

(defmulti -item-to-ssa (fn [x]
                        (println "item " x)
                        (debug (cond
                                (symbol? x) :symbol
                                (seq? x) :list
                                :else :default))))

(defn item-to-ssa [x]
  (-item-to-ssa (macroexpand x)))

(defmulti sexpr-to-ssa first)

(defmethod sexpr-to-ssa :default
  [args]
  (gen-plan
   [args-ids (all (map item-to-ssa args))
    inst-id (add-instruction (->Call args-ids))]
   inst-id))

(defn let-binding-to-ssa
  [[sym bind]]
  (println sym bind)
  (gen-plan
   [bind-id (item-to-ssa bind)
    _ (push-alter-binding :locals assoc sym bind-id)]
   bind-id))

(defmethod sexpr-to-ssa 'let*
  [[_ binds & body]]
  (let [parted (partition 2 binds)]
    (gen-plan
     [let-ids (all (map let-binding-to-ssa parted))
      body-ids (all (map item-to-ssa body))
      _ (all (map (fn [x]
                    (pop-binding :locals))
                  (range (count parted))))]
     (last body-ids))))

(defmethod sexpr-to-ssa 'loop*
  [[_ locals & body]]
  (let [parted (partition 2 locals)
        syms (map first parted)
        inits (map second parted)]
    (gen-plan
     [local-ids (all (map item-to-ssa inits))
      body-blk (add-block)
      final-blk (add-block)
      _ (add-instruction (->Jmp (last local-ids) body-blk))

      _ (set-block body-blk)
      _ (push-alter-binding :locals merge (debug  (zipmap (debug syms) (debug local-ids))))
      _ (push-binding :recur-point body-blk)
      _ (push-binding :recur-nodes local-ids)

      body-ids (all (map item-to-ssa body))

      _ (pop-binding :recur-nodes)
      _ (pop-binding :recur-point)
      _ (pop-binding :locals)
      _ (if (last body-ids)
          (add-instruction (->Jmp (last body-ids) final-blk))
          (no-op))

      _ (set-block final-blk)
      ret-id (add-instruction (->Const ::value))]
     ret-id)))

(defmethod sexpr-to-ssa 'do
  [[_ & body]]
  (gen-plan
   [ids (all (map item-to-ssa body))]
   (last ids)))

(defmethod sexpr-to-ssa 'recur
  [[_ & vals]]
  (gen-plan
   [val-ids (all (map item-to-ssa vals))
    recurs (get-binding :recur-nodes)
    _ (all (map #(add-instruction (->Set %1 %2))
                recurs
                val-ids))
    recur-point (get-binding :recur-point)
    
    _ (add-instruction (->Jmp nil recur-point))]
   nil))

(defmethod sexpr-to-ssa 'if
  [[_ test then else]]
  (gen-plan
   [test-id (item-to-ssa test)
    then-blk (add-block)
    else-blk (add-block)
    final-blk (add-block)
    _ (add-instruction (->CondBr test-id then-blk else-blk))
    
    _ (set-block then-blk)
    then-id (item-to-ssa then)
    _ (if then-id
        (gen-plan
         [_ (add-instruction (->Jmp then-id final-blk))]
         then-id)
        (no-op))

    _ (set-block else-blk)
    else-id (item-to-ssa else)
    _ (if else-id
        (gen-plan
         [_ (add-instruction (->Jmp else-id final-blk))]
         then-id)
        (no-op))

    _ (set-block final-blk)
    val-id (add-instruction (->Const ::value))]
   val-id))

(defmethod sexpr-to-ssa 'yield
  [[_ expr]]
  (gen-plan
   [next-blk (add-block)
    expr-id (item-to-ssa expr)
    jmp-id (add-instruction (->Await expr-id next-blk))
    _ (set-block next-blk)
    val-id (add-instruction (->Const ::value))]
   val-id))

(defmethod -item-to-ssa :list
  [lst]
  (sexpr-to-ssa lst))

(defmethod -item-to-ssa :default
  [x]
  (gen-plan
   [itm-id (add-instruction (->Const x))]
   itm-id))

(defmethod -item-to-ssa :symbol
  [x]
  (gen-plan
   [locals (get-binding :locals)
    inst-id (if (contains? locals x)
              (fn [p]
                [(locals x) p])
              (add-instruction (->Const x)))]
   inst-id))

(defn parse-to-state-machine [body]
  (-> (gen-plan
       [blk (add-block)
        _ (set-block blk)
        ids (all (map item-to-ssa body))
        term-id (add-instruction (->Return (last ids)))]
       term-id)
      get-plan
      debug))


(defn- build-block-preamble [state-sym blk]
  (let [args (->> (mapcat instruction-references blk)
                  set
                  vec)]
    (if (empty? args)
      []
      `({:keys ~args} ~state-sym))))

(defn- build-block-body [state-sym blk]
  (mapcat
   #(emit-instruction % state-sym)
   (butlast blk)))

(defn- build-new-state [state-sym blk]
  (let [results (concat (map :id (butlast blk))
                        (->> blk
                             (filter (comp (partial = :set) :type))
                             (map (comp first :args))))
        results (interleave (map keyword results) results)]
    (if-not (empty? results)
      `(assoc ~state-sym ~@results)
      state-sym)))

(defn- emit-state-machine [machine]
  (let [state-sym (gensym "state_")]
    `(fn [~state-sym]
       #_(pprint ~state-sym)
       (case (::state ~state-sym)
         nil
         (recur (assoc ~state-sym ::state ~(:start-block machine)))
         ~@(mapcat
            (fn [[id blk]]
              `(~(keyword id)
                (let [~@(concat (build-block-preamble state-sym blk)
                                (build-block-body state-sym blk))
                      ~state-sym ~(build-new-state state-sym blk)]
                  ~(emit-instruction (last blk) state-sym))))
            (:blocks machine))))))

(defmacro state-machine [& body]
  (-> (parse-to-state-machine body)
      second
      emit-state-machine
      debug))

(defn state-machine-seq
  ([f]
     (state-machine-seq f (f {})))
  ([f state]
      (if (= (::state state) ::finished)
        (cons (::value state) nil)
        (cons (::value state)
              (lazy-seq
               (state-machine-seq f (f state)))))))

(defn -main []
  (assert (= (-> (state-machine (let* [x (inc (yield 1))
                                         y (yield 1)]
                                        (+ x y)))
                   state-machine-seq
                   doall
                   debug)
               [1 1 3]))
  #_(assert (= (-> (state-machine (if (yield false)
                                    (yield true)
                                    (yield false)))
                   state-machine-seq
                   doall
                   debug)))
  
  #_(assert (= (-> (state-machine (loop [x 0]
                                    (if (< x 10)
                                      (recur (inc (yield x)))
                                      x)))
                   state-machine-seq
                   doall
                   debug)))

  #_(assert (= (->> (state-machine (do (yield 1)
                                     (yield 1)
                                     (loop [x2 1
                                            x1 1]
                                       (recur x1 (yield (+ x1 x2))))))
                  state-machine-seq
                  (take 32)
                  doall
                  debug)))

  
  )






