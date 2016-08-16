(ns typedmath.core-test
  (:require [clojure.test :refer :all]
            [typedmath.core :refer :all]))

(set! *warn-on-reflection* true)

;(def kattskiten 234)
;(println "Calling .toString should give us a reflection warning" (.toString kattskiten))


(deftest type-hinting-test
  (testing "Hinting"
    (let [xxy (fn [a b] (+ (* a a) (* b b)))
          xxy-hinted (fn [^double a ^double b] (+ a b))]
      (is (not (instance? java.lang.Double (xxy 3 4))))
      (is (instance? java.lang.Double (xxy-hinted 3 4))))
    (let [^"[D" A (double-array [3 4 5])]
      (is (= 4.0 (aget A 1))))
    (let [^"[D" B (make-array Double/TYPE 3)]
      (is (instance? java.lang.Double (aget B 0))))))


(deftest typedmath-test
  (testing "Inlining"
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

    (is (= {:type :number :expr 9}) (make-number-type 9))
    (is (= [{:type :number :value 9} {:type :number :value 11}])
        (compile-exprs {} [9 11] (fn [_ x] x)))

    (is (= [:this-is-a-number {:type :number :expr 9}]
               (compile-expr1 {} 9 (fn [x] [:this-is-a-number x]))))
    (is (= (compile-expr1 {} [1 2 3] identity)
               {:type :vector, :fields [{:type :number, :expr 1} 
                                        {:type :number, :expr 2} 
                                        {:type :number, :expr 3}]}))
    (is (= (compile-expr1 {} [[1 2] 3] identity)
               {:type :vector, :fields [{:type :vector, :fields 
                                         [{:type :number, :expr 1} 
                                          {:type :number, :expr 2}]} 
                                        {:type :number, :expr 3}]}))
    (is (= (compile-expr1 {} '(typed+ 1 2) identity)
               {:type :number, :expr 3}))

    (is (= (compile-expr1 {} '(typed+ [1 2 3] 4) identity)
               '{:type :vector, 
                 :fields [{:type :number, 
                           :expr 5} 
                          {:type :number, :expr 6} 
                          {:type :number, :expr 7}]}))
    (is (= [5 6 7]
           (eval (make-clojure-data 
                  (compile-expr1 {} '(typed+ [1 2 3] 4) identity)))))

    (is (= (replace-recursively {:a 3 :b 4} [:a :b])
           [3 4]))
    
    (is (= (compile-expr1 {} '(typed* 9 3) identity)
           '{:type :number :expr 27}))

    (is (= [-1 -2 -3] 
           (make-clojure-data
            (compile-expr1 {} '(typed- [5 4 3] 6) identity))))
    (is (= [2 4 8]
           (make-clojure-data
            (compile-expr1 {} '(typed* 2 [1 2 4]) identity))))

    (is (= (drop-data (compile-expr1 {} '[1 2 3] identity))
           {:type :vector, :fields [{:type :number} {:type :number} {:type :number}]}))

    (is (= 3 (flat-size (compile-expr1 {} '[1 2 3] identity))))
    (is (= [1 2 3 4 5] (flat-vector (compile-expr1 {} '[1 2 [[3] 4 5]] identity))))

    (is (= (populate {:type :number} [9])
           {:type :number :expr 9}))
    (let [my-type (drop-data (compile-expr1 {} '[1 [2 3]] identity))]
      (is (= my-type {:type :vector, :fields 
                      [{:type :number} {:type :vector, :fields 
                                        [{:type :number} {:type :number}]}]}))
      (is (= (compile-expr1 {} '[9 [20 119]] identity)
             (populate my-type [9 20 119]))))

    (is (= (compile-expr1 {} '[9 [4 5 6] 7 8 9] identity)
           (populate (drop-data (compile-expr1 {} '[0 [0 0 0] 0 0 0] identity))
                     [9 4 5 6 7 8 9])))
    (is (= 3 (get-primitive {:type :number :expr 3})))
    (is (= {:a 3} (compile-expr1 {} ''{:a 3} identity)))
    (is (= {:a 3} (compile-expr1 {} '(quote {:a 3}) identity)))
    (is (= (statically (output-value [3 4 5]))
           [3 4 5]))
    (is (= (statically [3 4 5])
           {:type :vector
            :fields [{:type :number, :expr 3} 
                     {:type :number, :expr 4} 
                     {:type :number, :expr 5}]}))
    (is (= [4 5 6] (statically (output-value (typed+ 1 [3 4 5])))))
    (is (= (bind-context {} 'rulle {:type :number :expr 3})
           {:bindings {'rulle {:type :number :expr 3}}}))
    (is (= (let [a 9] (statically (input-value {:type :number} a) a))
           {:type :number, :expr 9}))
    (is (= (let [a 9] (statically (input-value {:type :number} a)))
           {:type :number :expr 9}))
    (is (= (let [a 2
                 b 3]
             (statically 
              (input-value {:type :double} a)
              (input-value {:type :double} b)
              (typed+ a b)))
           {:type :double :expr 5}))
    (is (= (statically (typed+ (input-value {:type :double} 3) 
                               (input-value {:type :double} 4)))
           {:type :double, :expr 7}))
    (is (= (let [A [1 2 3 4]]
             (statically 
              (output-value
               (typed+ 
                9 (input-value {:type :vector 
                            :fields [{:type :number} 
                                     {:type :number} 
                                     {:type :number} 
                                     {:type :number}]} A)))))
           [10 11 12 13]))
    (is (= (sized-vector-type {:type :number} 3)
           '{:type :vector, :fields ({:type :number} {:type :number} {:type :number})}))

    (is (= (let [A [3 4 5]]
             (statically 
              (output-value
               (typed+
                9 (input-value (sized-vector-type {:type :number} 3) A)))))
           [12 13 14]))

    (is (= (Math/sin (* 0.25 Math/PI))
           (statically (output-value (Math/sin (* 0.25 Math/PI))))))

))


(deftest matrices
  (testing "Matrices"
    (is (= (+ 1 (* 2 3)) 
           (make-index-expr [1 2] [3 4])))

    (let [called (atom false)
          expr (make-ndarray-type 
                3 {:type :number} 'A 
                (fn [x]
                  (reset! called true)
                  (is (map? x))))]
      (is (seq? expr))
      (is (deref called)))
    
    (is (ndarray-expr? {:type :ndarray}))

    (let [arr (allocate-ndarray [2 3] {:type :double})]
      (is (= [2 3] (:dims arr)))
      (is (= 0 (:offset arr))))
    (let [mat (allocate-ndarray [2 3] {:type :double})
          x (statically 
             (input-value 
              (ndarray-type {:type :number} 2)
              mat))]
      (is (= :ndarray (:type x)))
      (is (= 0 (:offset x)))
      (is (= (:data x) (:data mat))))
    (is (= 9 (compute-index [1 2] [4 5])))

))










