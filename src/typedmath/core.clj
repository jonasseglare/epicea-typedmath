(ns typedmath.core)

(set! *warn-on-reflection* true)

;;;;;;;;;;;;;; UTILITIES
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

;;;;;;;;;;; METHODS AND FUNCTIONS ON TYPES ON THE DATA
;; If something is a scalar, in the mathematical sense. Not a vector or so...
(defn scalar? [x]
  (contains? #{:double :number :ad :complex} (:type x)))

(defmulti make-clojure-data :type :default nil)
(defmulti drop-data :type)
(defmulti flat-size :type)
(defmulti flat-vector :type)
;(defn flat-size [x] (count (flat-vector x)))
(defmulti populate (fn [x v] (:type x)))

;; Everything that in reality can be represented using just one primitive.
(templated
 [y]
 [[:number] 
  [:double]]
 (do
   (defmethod flat-vector y [x] [(:expr x)])
   (defmethod make-clojure-data y [x] (:expr x))
   (defmethod flat-size y [x] 1)
   (defmethod populate y [x v] (assoc x :expr (first v)))
   (defmethod drop-data y [x] (dissoc x :expr))))

(defn pop-field [acc next-field]
  {:populated 
   (conj (:populated acc) (populate next-field (:data acc)))
   :data 
   (drop (flat-size next-field) (:data acc))})

(defn populate-fields [fields v]
  (:populated
   (reduce 
    pop-field
    {:populated []
     :data v}
     fields)))
      
(defmethod make-clojure-data :vector [x] (mapv make-clojure-data (:fields x)))
(defmethod drop-data :vector [x] (update-in x [:fields] #(mapv drop-data %)))
(defmethod flat-size :vector [x] (apply + (map flat-size (:fields x))))
(defmethod flat-vector :vector [x] (vec (mapcat flat-vector (:fields x))))
(defmethod populate :vector [x v]
  (update x :fields #(populate-fields % v)))
          





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


(defn valid-arg-spec? [k] 
  (and (vector? k)
       (symbol? (second k))))

(defn valid-type-spec? [x]
  (and (vector? x)
       (every? valid-arg-spec? x)))

(defn test-arg-spec [arg-spec x]
  (assert (valid-arg-spec? arg-spec))
  (let [[a b] arg-spec]
    (if (keyword? a)
      (= a (:type x))
      (a x))))

(defn make-type-tester [types]
  (assert (valid-type-spec? types))
  (fn [args]
    (if (= (count types) (count args))
      (every?
       identity
       (map test-arg-spec
            types
            args)))))
            

(defn quote-symbols [spec]
  (mapv
   (fn [[a b]]
     [a (list 'quote b)])
   spec))


(defmacro def-typed-inline [name types cb & body]
  (assert (symbol? name))
  (assert (symbol? cb))
  `(add-typed-inline 
    (quote ~name)
    (make-type-tester ~(quote-symbols types))
    (fn [[~@(map second types)] ~cb]
      ~@body)))

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

(defmacro elementwise-left [op]
  `(def-typed-inline ~op [[:vector a#] [scalar? b#]] cb#
     (async-map
      (fn [field# cb0#] 
        (call-typed-inline (quote ~op) [field# b#] cb0#))
      (:fields a#)
      (fn [added#]
        (cb# {:type :vector
              :fields added#})))))

(defmacro elementwise-right [op]
  `(def-typed-inline ~op [[scalar? a#] [:vector b#]] cb#
     (async-map
      (fn [field# cb0#] 
        (call-typed-inline (quote ~op) [a# field#] cb0#))
      (:fields b#)
      (fn [added#]
        (cb# {:type :vector
              :fields added#})))))

(elementwise-left typed+)
(elementwise-left typed-)
(elementwise-left typed*)
(elementwise-left typed-div)
(elementwise-right typed+)
(elementwise-right typed-)
(elementwise-right typed*)
(elementwise-right typed-div)

nil

;(defn compile-exprs [frms]
;  (

;(defmacro statically [& frms]
;  (compile-exprs frms))
