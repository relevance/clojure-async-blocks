(ns async-tests.core
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [clojure.tools.namespace.repl :refer [refresh]]))


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
  (let [blk-sym (gensym "blk_")]
    (gen-plan
     [cur-blk (get-block)
      _ (assoc-in-plan [:blocks blk-sym] [])
      _ (if-not cur-blk
          (assoc-in-plan [:start-block] blk-sym)
          (no-op))]
     blk-sym)))

(defn add-instruction [inst & args]
  (let [inst-id (with-meta (gensym "inst_")
                  {::instruction true})
        inst {:type inst
              :args args
              :id inst-id}]
    (gen-plan
     [blk-id (get-block)
      _ (update-in-plan [:blocks blk-id] (fnil conj []) inst)]
     inst-id)))

(defn debug [x]
  (pprint x)
  x)

(defmulti item-to-ssa (fn [x]
                        (println "item " x)
                        (debug (cond
                                (symbol? x) :symbol
                                (seq? x) :list
                                :else :default))))

(defmulti sexpr-to-ssa first)

(defn let-binding-to-ssa
  [[sym bind]]
  (println sym bind)
  (gen-plan
   [bind-id (item-to-ssa bind)
    _ (push-alter-binding :locals assoc sym bind-id)]
   bind-id))

(defmethod sexpr-to-ssa :default
  [args]
  (gen-plan
   [args-ids (all (map item-to-ssa args))
    inst-id (apply add-instruction :call
                             args-ids)]
   inst-id))

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

(defmethod sexpr-to-ssa 'yield
  [[_ expr]]
  (gen-plan
   [next-blk (add-block)
    expr-id (item-to-ssa expr)
    jmp-id (add-instruction :yield expr-id next-blk)
    _ (set-block next-blk)
    val-id (add-instruction :let ::value)]
   val-id))

(defmethod item-to-ssa :list
  [lst]
  (sexpr-to-ssa lst))

(defmethod item-to-ssa :default
  [x]
  (fn [plan]
    [x plan]))

(defmethod item-to-ssa :symbol
  [x]
  (gen-plan
   [locals (get-binding :locals)]
   (do (println "locals" locals)
       (pprint locals)
       (if (contains? locals x)
         (locals x)
         x))))

(defn parse-to-state-machine [body]
  (-> (gen-plan
       [blk (add-block)
        _ (set-block blk)
        ids (all (map item-to-ssa body))
        term-id (add-instruction :return (last ids))]
       term-id)
      get-plan
      debug))


(defn- build-block-preamble [state-sym blk]
  (let [args (->> (mapcat :args blk)
                  debug
                  (filter symbol?)
                  (filter (comp ::instruction meta))
                  set
                  vec)]
    (if (empty? args)
      []
      `({:keys ~args} ~state-sym))))

(defn- build-terminator [state-sym {:keys [type args] :as inst}]
  (println type)
  (case type
    :yield
    `(assoc ~state-sym
       ::value ~(first args)
       ::state ~(keyword (second args)))
    :return
    `(assoc ~state-sym
       ::value ~(first args)
       ::state ::finished)))

(defn- build-block-body [state-sym blk]
  (mapcat
   (fn [inst]
     (case (:type inst)
       :let
       `(~(:id inst) ~(first (:args inst)))
       :call
       `(~(:id inst) ~(seq (:args inst)))))
   (butlast blk)))

(defn- build-new-state [state-sym blk]
  (let [results (map :id (butlast blk))
        results (interleave (map keyword results) results)]
    (if-not (empty? results)
      `(assoc ~state-sym ~@results)
      state-sym)))

(defn- emit-state-machine [machine]
  (let [state-sym (gensym "state_")]
    `(fn [~state-sym]
       (case (::state ~state-sym)
         nil
         (recur (assoc ~state-sym ::state ~(keyword (:start-block machine))))
         ~@(mapcat
            (fn [[id blk]]
              `(~(keyword id)
                (let [~@(concat (build-block-preamble state-sym blk)
                                (build-block-body state-sym blk))
                      ~state-sym ~(build-new-state state-sym blk)]
                  ~(build-terminator state-sym (last blk)))))
            (:blocks machine))))))

(defmacro state-machine [& body]
  (-> (parse-to-state-machine body)
      second
      emit-state-machine
      debug))

(defn -main []
  (let [x (state-machine (let* [x (inc (yield 1))
                                y (yield 1)]
                               (+ x y)))]
    (debug x)
    (debug (x {}))))






