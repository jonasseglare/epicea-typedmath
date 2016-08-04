(ns typedmath.core-test
  (:require [clojure.test :refer :all]
            [typedmath.core :refer :all]))


(deftest typedmath-test
  (testing "FIXME, I fail."
    (add-typed-inline 'dummy 
                      (fn [args]
                        (every? number? args))
                      :dummy-numbers)
    (is (= {:katt [119]} (conj-in-map {} :katt 119)))
    (is (= {:katt [119 120]} 
           (conj-in-map {:katt [119]} :katt 120)))
    (is (= :dummy-numbers
           (find-typed-inline 'dummy [1 2 3])))
    (is (nil? (find-typed-inline 'another-dummy [1 2 3])))
    (is (valid-type-spec? [[:number 'a] [:scalar 'b]]))
    (is (not (valid-type-spec? [[1] [:number 'b]])))
    (is ((make-type-tester [[:number 'a] [:number 'b]])
             [{:type :number :value 9} {:type :number :value 10}]))
    (is
     (not 
      ((make-type-tester [[:number 'a] [:scalar 'b]])
       [{:type :number :value 9} {:type :number :value 10}])))
    (is (= (call-typed-inline 'typed+ [{:type :number :expr 3}
                                       {:type :number :expr 4}] identity)
           {:type :number
            :expr 7}))

    (is (= {:type :number :expr 9}) (make-number 9))
    (is (= [{:type :number :value 9} {:type :number :value 11}])
        (compile-exprs [9 11] identity))

    (is (= [:this-is-a-number {:type :number :expr 9}]
               (compile-expr 9 (fn [x] [:this-is-a-number x]))))
    (is (= (compile-expr [1 2 3] identity)
               {:type :vector, :fields [{:type :number, :expr 1} 
                                        {:type :number, :expr 2} 
                                        {:type :number, :expr 3}]}))
    (is (= (compile-expr [[1 2] 3] identity)
               {:type :vector, :fields [{:type :vector, :fields 
                                         [{:type :number, :expr 1} 
                                          {:type :number, :expr 2}]} 
                                        {:type :number, :expr 3}]}))
    (is (= (compile-expr '(typed+ 1 2) identity)
               {:type :number, :expr 3}))

    (is (= (compile-expr '(typed+ [1 2 3] 4) identity)
               '{:type :vector, 
                 :fields [{:type :number, 
                           :expr 5} 
                          {:type :number, :expr 6} 
                          {:type :number, :expr 7}]}))
    (is (= [5 6 7]
           (eval (make-expression 
                  (compile-expr '(typed+ [1 2 3] 4) identity)))))

    (= (replace-recursively {:a 3 :b 4} [:a :b])
       [3 4])


))



