,(ns typedmath.index-loop-test
  (:require [typedmath.index-loop :refer :all])
  (:require [clojure.test :refer :all]))

(deftest index-loop-test
  (testing "Looping and indexing"
    (is (= '(:typedmath.index-loop/add 
             (:typedmath.index-loop/mul 
              3 9 (:typedmath.index-loop/add 4 5)) 4)
           (standardize '(+ (* 3 9 (+ 4 5)) 4))))
    (is (= (flatten-sub-expr '(:typedmath.index-loop/add a b))
           '(:typedmath.index-loop/add a b)))
    (is (= '(:typedmath.index-loop/add 1 2 3)
           (flatten-expr (standardize '(+ 1 (+ 2 3))))))
    (is (= (mul-2 '(:typedmath.index-loop/add  3 4) 
                  '(:typedmath.index-loop/add  5 6))
           '(:typedmath.index-loop/add 
             (:typedmath.index-loop/mul 3 5) 
             (:typedmath.index-loop/mul 3 6) 
             (:typedmath.index-loop/mul 4 5) 
             (:typedmath.index-loop/mul 4 6))))))
