(ns typedmath.index-loop-test
  (:require [typedmath.index-loop :refer :all])
  (:require [clojure.test :refer :all]))

(deftest index-loop-test
  (testing "Looping and indexing"
    (is (= '(:typedmath.index-loop/add 
             (:typedmath.index-loop/mul 
              3 9 (:typedmath.index-loop/add 4 5)) 4)
           (standardize '(+ (* 3 9 (+ 4 5)) 4))))))
