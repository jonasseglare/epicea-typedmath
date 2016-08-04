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

(defn make-double [x]
  (assert (number? x))
  {:type :double :expr x})

(defn conj-in-map [m key value]
  (if (contains? m key)
    (update-in m [key] #(conj % value))
    (assoc m key [value])))
               
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

(defn valid-type-spec? [x]
  (and (vector? x)
       (every? (fn [k] (and (vector? k)
                            (keyword? (first k))
                            (symbol? (second k)))) x)))

(defn make-type-tester [types]
  (fn [args]
    (if (= (count types) (count args))
      (every?
       (fn [[a b]] (= a b))
       (map vector 
            (map :type args)
            (map first types))))))


(defmacro def-typed-inline [name types cb & body]
  (assert (symbol? name))
  (assert (valid-type-spec? types))
  (assert (symbol? cb))
  `(add-typed-inline 
    (quote ~name)
    (make-type-tester (quote ~types))
    (fn [[~@(map second types)] ~cb]
      ~@body)))

(defn replace-recursively [replacement-map form]
  (clojure.walk/prewalk
   (fn [x]
     (if (contains? replacement-map x)
       (get replacement-map x) x))
   form))

(defmacro templated [symbols replacements form]
  (cons
   'do
   (map 
   (fn [rp]
     (replace-recursively
      (zipmap symbols rp)
      form))
   replacements)))

(templated 
 [left right result]
 [[:number :number :number]
  [:double :number :number]
  [:number :double :number]
  [:double :double :double]]
 (do
   (def-typed-inline typed+ [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(+ ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed- [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(- ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed* [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(* ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed-div [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(/ ~(:expr a) ~(:expr b)))}))))



(defn call-typed-inline [name args cb]
  (if-let [f (find-typed-inline name args)]
    (f args cb)
    (RuntimeException.
     (str "Didn't find function named " name " for arguments " args))))

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

(def-typed-inline typed+ [[:vector a] [:number b]] cb
  (async-map
   (fn [field cb] 
     (call-typed-inline 'typed+ [field b] cb))
   (:fields a)
   (fn [added]
     (cb {:type :vector
          :fields added}))))


(defmulti make-expression :type :default nil)

(templated
 [y]
 [[:number] 
  [:double]]
 (defmethod make-expression y [x] (:expr x)))

(defmethod make-expression :vector [x] (mapv make-expression (:fields x)))


;(defn compile-exprs [frms]
;  (

;(defmacro statically [& frms]
;  (compile-exprs frms))
