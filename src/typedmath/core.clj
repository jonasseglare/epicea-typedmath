(ns typedmath.core)

;; TODOs
;;   * type hint as many let-assignments as possible
;;   * implement 'to-data' for common matrix types
;;   * to-native-floats/from-native-floats
;;   * flatten nested let's and simplify but not beyond loops and functions.


(defn compilation-error [& s]
  (throw (RuntimeException. (apply str s))))

(defmacro disp [x]
  `(let [value# ~x] 
     (println (str "Value of " ~(str x) " is " value#))
     value#))

(defn always-true [x] true)

;(set! *warn-on-reflection* true)
(set! *warn-on-reflection* true)

;; Core types

;; Represents something not known at compile time.
(defn make-dynamic-type [x]
  {:type :dynamic :expr x})

;; Represents any number on the host platform.
(defn make-number-type [x]
  (assert (number? x))
  {:type :number :expr x})

;;;;;;;;;;;;;; UTILITIES
(defn precompute [x]
  (try
    (eval x)
    (catch Throwable e x)))

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

(defmulti make-from-data (fn [x sym cb] (:type x)))

(defn sized-vector [type n]
  {:type :vector
   :fields (repeat n type)})

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

(def-typed-inline to-data [[always-true x]] cb
  (cb (make-clojure-data x)))

(defn call-typed-inline [name args cb]
  (if-let [f (find-typed-inline name args)]
    (f args cb)
    (compilation-error
     "Didn't find function named " name " for arguments " args)))

(declare compile-expr2)
(declare compile-expr1)

(defn async-map-sub [f args acc cb]
  (if (empty? args)
    (cb acc)
    (f
     (first args)
     (fn [arg]
       (async-map-sub f (rest args) (conj acc arg) cb)))))

(defn async-map [f args cb]
  (async-map-sub f args [] cb))

(defn compile-exprs-sub [acc context exprs cb]
  (if (empty? exprs)
    (cb context acc )
    (compile-expr2 
     context 
     (first exprs)
     (fn [next-context x]
       (compile-exprs-sub (conj acc x) next-context (rest exprs) cb)))))

;; Used to compile a sequence of exprs. The compiled
;; exprs are passed as a vector to the callback cb.
(defn compile-exprs [context exprs cb]
  (compile-exprs-sub [] context exprs cb))

  ;; (async-map (fn [x cb] 
  ;;              (compile-expr1 context x cb))
  ;;            exprs
  ;;            cb))

(defn make-vector [context v0 cb2]
  (compile-exprs 
   context
   v0 (fn [c2 v] (cb2 c2 {:type :vector :fields v}))))

(defn typed-inline-call? [x]
  (and (seq? x)
       (not (nil? (find-typed-inline (first x)
                                     (rest x))))))

(defn make-typed-inline-call [[name & args] cb]
  (call-typed-inline name args cb))

(declare from-data)

(defn pass-on-context [context cb]
  (fn [x] (cb context x)))

(defn bind-context [context sym x]
  (assoc-in context [:bindings sym] x))

(defn compile-spec [context args cb2]
  (let [[type-spec0 sym] args
        type-spec (eval type-spec0)]
    (make-from-data 
     type-spec sym 
     (fn [value]
       (assert (map? type-spec))
       (if (symbol? sym)
         (cb2 (bind-context context sym value) value)
         (cb2 context value))))))

(defn compile-list-form [context x cb2]
  ;; Currently, only typed calls.
  (let [[name & args] x]
    (cond
      (= 'from-data name) (compile-spec context args cb2)
      (= 'quote name) (first args)

      :default
      (compile-exprs 
       context
       args
       (fn [next-context cargs]
         (call-typed-inline 
          name cargs 
          (fn [x] (cb2 next-context x))))))))

(defn compile-symbol [context x]
  (let [b (:bindings context)]
    (if (contains? b x)
      (get b x)
      (make-dynamic-type x))))


(defn compile-expr2 [context x cb2]
  (cond
    (number? x) (cb2 context (make-number-type x))
    (symbol? x) (cb2 context (compile-symbol context x))
    (vector? x) (make-vector context x cb2)
    (list? x) (compile-list-form context x cb2)
    :default (compilation-error "Failed to compile: " x)))

(defn compile-expr1 [context x cb1]
  (compile-expr2 context x (fn [_ out] (cb1 out))))












;;;;;;;;;;;;;;;;;;;;;;;;;;; MORE TYPES
(defn make-double [x]
  (assert (number? x))
  {:type :double :expr x})

(defn make-num-from-sym [spec x]
  (assoc spec :expr x))
(defmethod make-from-data :number [spec x cb] (cb (make-num-from-sym spec x)))
(defmethod make-from-data :double [spec x cb] (cb (make-num-from-sym spec x)))
(defmethod make-from-data :vector [spec x cb] 
  (async-map (fn [[field i] cb]
               (let [s (gensym)]
               `(let [~s (nth ~x ~i)] ;; TODO: Type hint s here based on the type of field?
                  ~(make-from-data field s cb))))
             (map vector (:fields spec) (range (count (:fields spec))))
             (fn [result]
               (cb (assoc spec :fields result)))))

(templated 
 [left right result]
 [[:number :number :number]
  [:double :number :number]
  [:number :double :number]
  [:double :double :double]]
 (do
   (def-typed-inline typed+ [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(unchecked-add ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed- [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(unchecked-subtract ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed* [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(unchecked-multiply ~(:expr a) ~(:expr b)))}))
   (def-typed-inline typed-div [[left a] [right b]] cb
     (cb {:type result
          :expr (precompute `(unchecked-divide ~(:expr a) ~(:expr b)))}))))

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

;; Runtime type for nd-arrays
(defrecord NDArray [dims data elem-type])

(defn acc-index-expr [acc index-expr]
  {:expr 
   (precompute 
    `(unchecked-add 
     ~index-expr 
     ~(precompute `(unchecked-multiply ~(first (:dims acc)) ~(:expr acc)))))
   :dims (rest (:dims acc))})

(defn make-index-expr [inds dims]
  (assert (vector? inds))
  (assert (vector? dims))
  (:expr 
   (reduce
    acc-index-expr
    {:expr 0
     :dims (reverse dims)}
    (reverse inds))))
  
(defn get-primitive [x]
  (let [x (flat-vector x)]
    (assert (= 1 (count x)))
    (first x)))

(defn make-ndarray-type [dim-count elem-type sym cb]
  (assert (number? dim-count))
  (let [elem-size (flat-size elem-type)
        size-symbol (gensym)
        dims (conj 
              (map 
               (fn [x] `(nth ~size-symbol ~x)) 
               (range dim-count)) elem-size)
        dim-symbols (take dim-count (repeatedly gensym))
        dim-exprs (conj dim-symbols elem-size)
        data-symbol (gensym)
        index-fn (fn [inds] (make-index-expr (vec inds) (vec dim-exprs)))
        get-primitive-expr (fn [inds] 
                             `(aget ~data-symbol ~(index-fn inds)))
        get-flat-element (fn [inds] 
                           (map (fn [i] 
                                  (get-primitive-expr
                                   (conj inds i)))
                                (range elem-size)))
        get-element (fn [inds] (populate elem-type (vec (get-flat-element inds))))]
    `(let [^"[D" ~data-symbol (:data ~sym)
           ~size-symbol (:dims ~sym)
           ~@(mapcat (fn [x y] [^int x y]) dim-symbols dims)]
       ~(cb {:type :ndarray
            :dims dim-symbols
            :get-element-fn get-element}))))


(defn numeric-constant? [x]
  (number? (:expr x)))

(defn get-numeric-constant [x]
  (:expr x))

;; (def-typed-inline ndarray [[numeric-constant? dim-count]
;;                            [always-true element-type]
;;                            [:dynamic src]] cb
;;   (cb {:type :ndarray
;;        :dim-count (get-numeric-constant dim-count)
;;        :dims-expr-fn (fn [] `(:dims ~src))
;;        :dim-expr-fn (fn [index] `(nth (:dims ~src) ~index))
;;        :index-expr-fn (fn [inds] )}))

(def-typed-inline typed+ [[:ndarray A]
                          [:ndarray B]] cb
  (cb {:type :add
       :left A
       :right B}))

(def-typed-inline typed* [[:ndarray A]
                          [:ndarray B]] cb
  (cb {:type :matmul
       :left A
       :right B}))

(def-typed-inline typed- [[:ndarray A]
                          [:ndarray B]] cb
  (cb {:type :sub
       :left A
       :right B}))

(def-typed-inline typed- [[:ndarray A]] cb
  (cb {:type :neg
       :value A}))

(def-typed-inline typed-transpose [[:ndarray A]] cb
  (cb {:type :transpose
       :value A}))

;; The second argument is the callback, and that callback gets called for every
;; element that is evaluated.
(defmulti evaluate-mat-expr (fn [a _] (:type a)))

(defn evaluate-mat-add-1 [A B cb]
  (cb :nothing))

(defmethod evaluate-mat-expr :add [expr cb]
  (let [{:keys [A B]} expr]
    (assert (= (:dims A) (:dims B)))
    (if (= 1 (:dims A))
      (evaluate-mat-add-1 A B cb))))

(defn statically-sub [context forms]
  (if (empty? forms)
    nil
    (compile-expr2 
     context
     (first forms)
     (fn [next-context x]
       (let [k (rest forms)]
         (if (empty? k) x
             (statically-sub next-context k)))))))

(defmacro statically [& frms]
  (statically-sub {} frms))
