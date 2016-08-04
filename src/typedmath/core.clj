(ns typedmath.core)

(set! *warn-on-reflection* true)

(defn precompute [x]
  (try
    (eval x)
    (catch Throwable e x)))

;; Represents something not known at compile time.
(defn make-dynamic [x]
  {:type :dynamic :expr x})

;; Represents any number on the host platform.
(defn make-number [x]
  (assert (number? x))
  {:type :number :expr x})

(defn conj-in-map [m key value]
  (if (contains? m key)
    (update-in m [key] #(conj % value))
    (assoc m key [value])))

(assert (= {:katt [119]} (conj-in-map {} :katt 119)))
(assert (= {:katt [119 120]} 
           (conj-in-map {:katt [119]} :katt 120)))
               
;; A look-up table of defined functions
(let [table (atom {})]
  (defn add-typed-inline [name tester? fun]
    (swap! table #(conj-in-map % name [tester? fun])))

  (defn find-typed-inline [name args]
    (if-let [[tester? fun]
             (first
              (filter 
               (fn [[tester? fun]]
                 (if (tester? args) fun))
               (get (deref table) name)))]
             fun)))

(add-typed-inline 'dummy 
                     (fn [args]
                       (every? number? args))
                     :dummy-numbers)

(assert (= :dummy-numbers
           (find-typed-inline 'dummy [1 2 3])))
(assert (nil? (find-typed-inline 'another-dummy [1 2 3])))

(defn valid-type-spec? [x]
  (and (vector? x)
       (every? (fn [k] (and (vector? k)
                            (keyword? (first k))
                            (symbol? (second k)))) x)))

(assert (valid-type-spec? [[:number 'a] [:scalar 'b]]))
(assert (not (valid-type-spec? [[1] [:number 'b]])))

(defn make-type-tester [types]
  (fn [args]
    (if (= (count types) (count args))
      (every?
       (fn [[a b]] (= a b))
       (map vector 
            (map :type args)
            (map first types))))))

(assert ((make-type-tester [[:number 'a] [:number 'b]])
         [{:type :number :value 9} {:type :number :value 10}]))
(assert 
 (not 
  ((make-type-tester [[:number 'a] [:scalar 'b]])
   [{:type :number :value 9} {:type :number :value 10}])))

(defmacro def-typed-inline [name types cb & body]
  (assert (symbol? name))
  (assert (valid-type-spec? types))
  (assert (symbol? cb))
  `(add-typed-inline 
    (quote ~name)
    (make-type-tester (quote ~types))
    (fn [[~@(map second types)] ~cb]
      ~@body)))

(def-typed-inline typed+ [[:number a] [:number b]] cb
  (cb {:type :number
       :expr (precompute `(+ ~(:expr a) ~(:expr b)))}))

(defn call-typed-inline [name args cb]
  (if-let [f (find-typed-inline name args)]
    (f args cb)
    (RuntimeException.
     (str "Didn't find function named " name " for arguments " args))))

(assert (= (call-typed-inline 'typed+ [{:type :number :expr 3}
                                       {:type :number :expr 4}] identity)
           {:type :number
            :expr 7}))

(assert (= {:type :number :expr 9}) (make-number 9))

(declare compile-expr)

(defn async-map-sub [f args acc cb]
  (if (empty? args)
    (cb acc)
    (f
     (first args)
     (fn [arg]
       (async-map-sub f (rest args) (conj acc arg) cb)))))

(defn async-map [f args cb]
  (async-map-sub f args [] cb))

;; Used to compile a sequence of exprs. The compiled
;; exprs are passed as a vector to the callback cb.
(defn compile-exprs [exprs cb]
  (async-map compile-expr exprs cb))

(assert (= [{:type :number :value 9} {:type :number :value 11}])
        (compile-exprs [9 11] identity))

(defn make-vector [v0 cb]
  (compile-exprs 
   v0 (fn [v] (cb {:type :vector :fields v}))))

(defn typed-inline-call? [x]
  (and (seq? x)
       (not (nil? (find-typed-inline (first x)
                                     (rest x))))))

(defn make-typed-inline-call [[name & args] cb]
  (call-typed-inline name args cb))

(defn compile-list-form [x cb]
  ;; Currently, only typed calls.
  (let [[name & args] x]
    (compile-exprs 
     args
     (fn [cargs]
       (call-typed-inline name cargs cb)))))
  
(defn compile-expr [x cb]
  (cond
    (number? x) (cb (make-number x))
    (symbol? x) (cb (make-dynamic x))
    (vector? x) (make-vector x cb)
    (list? x) (compile-list-form x cb)
    :default (RuntimeException. (str "Failed to compile: " x))))

(assert (= [:this-is-a-number {:type :number :expr 9}]
           (compile-expr 9 (fn [x] [:this-is-a-number x]))))
(assert (= (compile-expr [1 2 3] identity)
           {:type :vector, :fields [{:type :number, :expr 1} 
                                    {:type :number, :expr 2} 
                                    {:type :number, :expr 3}]}))
(assert (= (compile-expr [[1 2] 3] identity)
           {:type :vector, :fields [{:type :vector, :fields 
                                     [{:type :number, :expr 1} 
                                      {:type :number, :expr 2}]} 
                                    {:type :number, :expr 3}]}))
(assert (= (compile-expr '(typed+ 1 2) identity)
           {:type :number, :expr 3}))



(def-typed-inline typed+ [[:vector a] [:number b]] cb
  (async-map
   (fn [field cb] 
     (call-typed-inline 'typed+ [field b] cb))
   (:fields a)
   (fn [added]
     (cb {:type :vector
          :fields added}))))

(assert (= (compile-expr '(typed+ [1 2 3] 4) identity)
           '{:type :vector, 
            :fields [{:type :number, 
                      :expr 5} 
                     {:type :number, :expr 6} 
                     {:type :number, :expr 7}]}))

(defmulti make-expression :type :default nil)
(defmethod make-expression :number [x] (:expr x))
(defmethod make-expression :vector [x] (mapv make-expression (:fields x)))

(assert (= [5 6 7]
           (eval (make-expression 
                  (compile-expr '(typed+ [1 2 3] 4) identity)))))

;(defn compile-exprs [frms]
;  (

;(defmacro statically [& frms]
;  (compile-exprs frms))
