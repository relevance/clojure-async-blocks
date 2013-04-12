# async-tests

This is Tim B's working space for async blocks in Clojure. 

If you are familiar at all with Async/await in C# 5 (or Scala) this is more or less the exact same thing. This library translates normal clojure code into a state machine that can pause and be resumed anywhere in the block. After translating code into this state machine format, it can be consumed by several wrappers that present different interfaces to this state machine. 

Currently there are three such wrappers:

runner-wrapper - Does nothing but run the state-machine as the code would normally be run. Useful for debugging the output of the code.

async-wrapper - Each time deref is called on a future in a block, the next state of the machine is connected to the future. This allows "normal" looking code to be executed in an async manner. 

seq-wrapper - This takes the result of each state and returns it as an item in a lazy-seq. 



Example: 

    (= [0 1 1 2 3 5 8 13 21 34 55 89]
       (take 12 (generator (yield 0)
                           (loop [x2 (yield 1)
                                  x1 (yield 1)]
                                 (recur x1 (yield (+ x1 x2)))))))



Async example:

(in these examples, cqe refer's to Stuart's Cljque library)

    (defn defer [value]
      (cqe/future value))



    (deftest async-test
      (testing "values are returned correctly"
        (is (= 10
               @(async @(defer 10)))))
      (testing "supports hash map literals"
        (is (= {:a 42 :b 43}
               @(async {:a @(defer 42)
                        :b @(defer 43)}))))
      (testing "supports atom derefs"
        (is (= {:a 42 :b 43}
               @(async {:a @(defer 42)
                        :b @(atom 43)})))))

