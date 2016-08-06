(ns typedmath.index-loop)

(def array-index identity)

(defn make-index-loop [loop-var iter-count body]
  `(loop [^int ~loop-var 0]
     (when (< ~loop-var ~iter-count)
       ~@body
       (recur (unchecked-add 1 ~loop-var)))))


(defmacro index-loop [[loop-var iter-count] & body]
  (make-index-loop loop-var iter-count body))

(def ops {'unchecked-add ::add
          'unchecked-add-int ::add
          '+ ::add
          ::add ::add
          '* ::mul
          'unchecked-multiply ::mul
          'unchecked-multiply-int ::mul
          ::mul ::mul})

;(defmulti standardize (fn [x] (if (list? x) (get ops (first x)) nil)))

(defn map-op [x]
  (if (contains? ops x) (get ops x) x))

(defn standardize [x]  
  (clojure.walk/postwalk
   (fn [x] (if (list? x) `(~(map-op (first x)) ~@(rest x)) x))
   x))

(defn get-tag [x] (if (seq? x) (first x)))

(defmulti flatten-sub-expr get-tag)

(defn add-2 [a b]
  (println "add-2 called on " a " and " b)
  (if (= ::add (get-tag a))
    (if (= ::add (get-tag b))
      `(::add ~@(rest a) ~@(rest b))
      `(::add ~@(rest a) ~b))
    (if (= ::add (get-tag b))
      `(::add ~a ~@(rest b))
      `(::add ~a ~b))))

(defmethod flatten-sub-expr ::add [x]
  (reduce add-2 (rest x)))

(defn cart [colls]
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cart (rest colls))]
      (cons x more))))

(defn mul-sums [a b]
  (cons ::add (map #(cons ::mul %) (cart [a b]))))

(defn mul-2 [a b]
  (cond
    (= ::add (get-tag a))
    (cond 
      (= ::add (get-tag b))
      (mul-sums (rest a) (rest b))

      (= ::mul (get-tag b))
      (cons ::add (map (fn [x] `(::mul ~x ~@(rest b)) (rest a)))))))
                         
      
          

(defmethod flatten-sub-expr ::mul [x]
  (reduce mul-2 (rest x)))

(defmethod flatten-sub-expr nil [x] x)

(defn flatten-expr [x]
  (clojure.walk/postwalk
   flatten-sub-expr x))

;;(defn contains-loop-var [expr loop-variable]
;;  (

;; (defn simplify [expr loop-variable]
;;   (cond
;;     (seq? expr) (simplify-seq expr loop-variable)
;;     :default {:bindings 
;;               :expr expr}))
