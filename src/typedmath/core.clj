(ns typedmath.core
  (:require [typedmath.index-loop :refer :all]))

(defn compilation-error [& s]
  (throw (RuntimeException. (apply str s))))



;; TODOs
;;   * type hint as many let-assignments as possible
;;   * implement 'to-data' for common matrix types
;;   * to-native-floats/from-native-floats
;;   * flatten nested let's and simplify but not beyond loops and functions.
;;   * use the espresso library for simplifying indices.

(def platform-spec 
  (atom
   {:add {:long 'unchecked-add-int
          :int 'unchecked-add-int
          :double 'unchecked-add}
    :mul {:long 'unchecked-multiply-int
          :int 'unchecked-multiply-int
          :double 'unchecked-multiply}
    :sub {:long 'unchecked-subtract-int
          :int 'unchecked-subtract-int
          :double 'unchecked-subtract}
    :div {:long 'unchecked-divide-int
          :int 'unchecked-divide-int
          :double /}
    :neg {:long 'unchecked-negate-int
          :int 'unchecked-negate-int
          :double 'unchecked-negate}}))

(defn get-op [what type]
  (let [spec (deref platform-spec)]
    (if-let [per-type (get spec what)]
      (if (contains? per-type type)
        (get per-type type)
        (compilation-error "Missing operation for type " type " in " per-type))
      (compilation-error "Missing operations for " what))))

(defmacro add [type a b]
  (cond
    (= 0 a) b
    (= 0 b) a
    :default `(~(get-op :add type) ~a ~b)))

(defmacro mul [type a b]
  (cond
    (= 1 a) b
    (= 1 b) a
    :default `(~(get-op :mul type) ~a ~b)))

(defn type-hint-symbol [sym tag]
  (vary-meta sym assoc :tag tag))

(defmacro disp [x]
  `(let [value# ~x] 
     (println (str "Value of " ~(str x) " is " value#))
     value#))

(defn dont-care [x] true)

;(set! *warn-on-reflection* true)
(set! *warn-on-reflection* true)

;; Core types

;; Represents something not known at compile time.
(defn make-dynamic-type [x]
  {:type :dynamic :expr x})

;; Represents any number on the host platform.
(defn make-number-type [x]
  (assert (number? x))
  {:type :double :expr x})

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
  (contains? #{:double :ad :complex} (:type x)))

(defn array-like? [x]
  (contains? #{:ndarray} (:type x)))

(defmulti make-clojure-data :type :default nil)
(defmulti drop-data :type)
(defmulti flat-size :type)
(defmulti flat-vector :type)
;(defn flat-size [x] (count (flat-vector x)))
(defmulti populate (fn [x v] (:type x)))

(defmulti make-input-value (fn [x sym cb] (:type x)))

(defn sized-vector-type [type n]
  {:type :vector
   :fields (repeat n type)})

;; Everything that in reality can be represented using just one primitive.
(defmethod make-clojure-data :dynamic [x] (:expr x))

(templated
 [y]
 [[:double] 
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

(defn arg-count-is-at-least [n]
  (fn [args]
    (<= n (count args))))


(defn resolve-reduced-sub [name args cb]
  (let [first-args (take 2 args)
        rest-args (drop 2 args)
        f (find-typed-inline name first-args)]
    (if (nil? f)
      (compilation-error "Failed to resolve " name " for arguments " (vec first-args))
      (f first-args
         (fn [result]
           (if (empty? rest-args)
             (cb result)
             (resolve-reduced-sub name (conj rest-args result) cb)))))))

(defn resolve-reduced [name]
  (fn [args cb]
    (resolve-reduced-sub name args cb)))


(defmacro def-typed-reduced [name]
  `(add-typed-inline
    (quote ~name)
    (arg-count-is-at-least 3)
    (resolve-reduced (quote ~name))))

(def-typed-inline output-value [[dont-care x]] cb
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
    (cb context acc)
    (compile-expr2 
     context 
     (first exprs)
     (fn [next-context x]
       (compile-exprs-sub (conj acc x) next-context (rest exprs) cb)))))

;; Used to compile a sequence of exprs. The compiled
;; exprs are passed as a vector to the callback cb.
(defn compile-exprs [context exprs cb]
  (assert (fn? cb))
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

(declare input-value)

(defn pass-on-context [context cb]
  (fn [x] (cb context x)))

(defn bind-context [context sym x]
  (assoc-in context [:bindings sym] x))

(let [table (atom {})]
  (defn add-call-by-expr [name fun]
    (swap! table #(assoc % name fun)))
  (defn find-call-by-expr [name]
    (get (deref table) name)))

(defmacro def-call-by-expr [name args & body]
  `(add-call-by-expr (quote ~name) (fn [~@args] ~@body)))


(defn ensure-simple-expr [x cb]
  (if (not (coll? x))
    (cb x)
    (let [s (gensym)]
      `(let [~s ~x]
         ~(cb s)))))



(def-call-by-expr input-value [context args cb2]
  (let [[type-spec0 sym0] args
        type-spec (eval type-spec0)]
    (ensure-simple-expr 
     sym0
     (fn [sym]
       (make-input-value 
        type-spec sym 
        (fn [value]
          (assert (map? type-spec))
          (if (symbol? sym)
            (cb2 (bind-context context sym value) value)
            (cb2 context value))))))))

(defn attempt-call-typed-inline [context fun args cb2]
  (compile-exprs 
   context
   args
   (fn [next-context cargs]
     (fun cargs (fn [x] (cb2 next-context x))))))

(defn compile-list-form-for-compiled-args [context name cargs cb]
  ;; Third thing to try: Is it a typed-inline?
  (if-let [typed-inline (find-typed-inline name cargs)]
    (typed-inline cargs (pass-on-context context cb))

    ;; Fourth thing: Try to invoke it as a regular function.
    ;; Checking whether such a function exists might not be easy
    ;; because it could be a bound local variable in the enclosing
    ;; expression.
    (cb context
        (make-dynamic-type ;; Tag it as dynamic type: We don't know
         ;; what the function returns.
         `(~name ~@(map make-clojure-data cargs))))))


(defn compile-list-form [context0 x cb2]
  (let [[name & args] x]
    ;; First thing to try: Is it quoted?
    (if (= 'quote name) 
      (first args)

      ;; Second thing to try: Is it a call-by-expr?
      (if-let [call-by-expr (find-call-by-expr name)]
        (call-by-expr context0 args cb2)

        (compile-exprs
         context0 args
         (fn [context1 cargs]
           (compile-list-form-for-compiled-args
            context1 name cargs cb2)))))))

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












;;;;;;;;;;;;;;;;;;;;;;;;;;; MORE TYPES
(defn make-double [x]
  (assert (number? x))
  {:type :double :expr x})

(defn make-num-from-sym [spec x]
  (assoc spec :expr x))
(defmethod make-input-value :double [spec x cb] (cb (make-num-from-sym spec x)))
(defmethod make-input-value :double [spec x cb] (cb (make-num-from-sym spec x)))
(defmethod make-input-value :vector [spec x cb] 
  (async-map (fn [[field i] cb]
               (let [s (gensym)]
               `(let [~s (nth ~x ~i)] ;; TODO: Type hint s here based on the type of field?
                  ~(make-input-value field s cb))))
             (map vector (:fields spec) (range (count (:fields spec))))
             (fn [result]
               (cb (assoc spec :fields result)))))

(templated 
 [left right result]
 [[:double :double :double]]
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
(def-typed-reduced typed+)
(def-typed-reduced typed-)
(def-typed-reduced typed*)
(templated
 [input output]
 [[:double :double]]
 (def-typed-inline typed- [[input x]] cb
   (cb {:type output
        :expr (precompute `(unchecked-negate ~(:expr x)))})))


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
(defrecord NDArray [offset dims steps data elem-type])

;;;;;;;; NDArray runtime ops
(defn allocate-ndarray [dims elem-type]
  (let [n (count dims)]
    (->NDArray 0
               dims
               dims
               (double-array (* (apply * dims) (flat-size elem-type)))
               elem-type)))

(defn compute-index [inds dims]
  (assert (= (count inds) (count dims)))
  (if (empty? inds)
    0
    (+ (first inds)
       (* (first dims)
          (compute-index (rest inds)
                         (rest dims))))))

(defn set-element [mat inds data]
  (let [esize (flat-size (:elem-type mat))
        index (compute-index 
               (cons 0 inds)
               (cons esize (:dims mat)))]
    (assert (= esize (count data)))
    (let [^"[D" dst(:data mat)]
      (index-loop [k esize]
                  (aset dst (+ index k) (double (nth data k)))))))
    






;;;;;;;;; NDArray macro-expansion time ops
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
             :data data-symbol
             :offset 0
             :dim-count dim-count
             :elem-type elem-type
             :get-element-fn get-element}))))


(defn numeric-constant? [x]
  (number? (:expr x)))

(defn get-numeric-constant [x]
  (:expr x))

;; (def-typed-inline ndarray [[numeric-constant? dim-count]
;;                            [dont-care element-type]
;;                            [:dynamic src]] cb
;;   (cb {:type :ndarray
;;        :dim-count (get-numeric-constant dim-count)
;;        :dims-expr-fn (fn [] `(:dims ~src))
;;        :dim-expr-fn (fn [index] `(nth (:dims ~src) ~index))
;;        :index-expr-fn (fn [inds] )}))


(def-typed-inline typed-transpose [[:ndarray A]] cb
  (cb {:type :transpose
       :value A}))

(def-typed-inline disp-value [[dont-care x]] cb
  `(do (println "  Value " ~(:expr x)) 
       ~@(cb nil)))

(defn gensyms [n]
  (vec (take n (repeatedly gensym))))

(defn make-actual-steps [current-step steps]
  (if (empty? steps)
    '()
    (let [s (gensym)]
      (cons [s current-step]
            (make-actual-steps 
             `(clojure.core/unchecked-multiply-int ~s ~(first steps))
             (rest steps))))))

(defn make-input-value-ndarray [spec sym cb]
  (let [[offset data] (repeatedly gensym)
        dim-count (:dim-count spec)
        step-syms (gensyms dim-count)
        dim-syms (gensyms dim-count)
        actual-steps (make-actual-steps (flat-size (:elem-type spec)) step-syms)]
    `(let [~offset (:offset ~sym)
           ~dim-syms (:dims ~sym)
           ~step-syms (:steps ~sym)
           ~@(apply concat actual-steps)
           ~(type-hint-symbol data "[D") (:data ~sym)]
       ~(cb (merge spec
                   {:offset offset
                    :dim-syms dim-syms
                    :step-syms step-syms
                    :data data
                    :actual-steps (vec (map first actual-steps))})))))

       

(defmethod make-input-value :ndarray [spec sym cb]
  (make-input-value-ndarray spec sym cb))
  

(defn ndarray-expr? [x]
  (contains?
   #{:ndarray}
   (:type x)))

(defmulti split-outer (fn [matexpr sym cb] (:type matexpr)))
(defmulti per-element-op :type)
(defmulti get-single-element :type)

(defmacro compute-offset [old-offset step index]
  `(add :long ~old-offset (mul :long ~step ~index)))

(defn split-outer-ndarray [mat sym cb]
; (type-hint-symbol (gensym) 'int)]
; CompilerException java.lang.UnsupportedOperationException: Can't type hint a local with a primitive initializer, compiling:(*cider-repl typedmath*:200:16) 
  (let [offset (gensym)] 

    `(let [~offset (compute-offset ~(:offset mat) ~(last (:actual-steps mat)) ~sym)]
       ~(cb (merge mat {:offset offset
                        :dim-count (dec (:dim-count mat))
                        :dim-syms (butlast (:dim-syms mat))
                        :step-syms (butlast (:step-syms mat))
                        :actual-steps (butlast (:actual-steps mat))})))))
    

(defmethod split-outer :ndarray [mat sym cb]
  (split-outer-ndarray mat sym cb))

(defn list-agets [arr offset n]
  (assert (symbol? arr))
  (assert (or (number? offset) (symbol? offset)))
  (assert (number? n))
  (map (fn [i] `(aget ~arr (add :long ~offset ~i))) (range n)))

(defn list-ndarray-agets [mat]
  (let [etype (:elem-type mat)]
    (list-agets (:data mat) (:offset mat) (flat-size etype))))

(defmethod per-element-op :ndarray [mat]
  (populate (:elem-type mat (list-ndarray-agets mat))))

(defn get-single-ndarray-element [mat]
  (assoc 
   (populate (:elem-type mat) (list-ndarray-agets mat))
   :storage mat))
  

(defmethod get-single-element :ndarray [mat]
  (get-single-ndarray-element mat))


(defn make-full-array-loop [mat]
  (assert (every? symbol? (:dim-syms mat)))
  (if (empty? (:dim-syms mat))
    (per-element-op mat)
    (let [loop-var (gensym)]
      `(index-loop 
        [~loop-var ~(last (:dim-syms mat))]
        ~(split-outer 
           mat loop-var
           make-full-array-loop)))))

(def-typed-inline array-loop [[:ndarray A]] cb
  (cb (make-full-array-loop A)))

(defn per-element-op-ewise [mat]
  (let [args (map get-single-element (:args mat))]
    (compile-list-form-for-compiled-args
     {}
     (:op mat) args (fn [a b] b))))

(defmethod per-element-op :element-wise [mat]
  (per-element-op-ewise mat))


(defn split-outer-args [args sym cb]
  (async-map #(split-outer %1 sym %2) args cb))

(defn split-outer-element-wise [mat sym cb]
  (split-outer-args 
   (:args mat) sym
   (fn [args]
     (cb (merge mat {:dim-syms (butlast (:dim-syms mat))
                     :args args})))))
   

(defmethod split-outer :element-wise [mat sym cb]
  (split-outer-element-wise mat sym cb))

(defn element-wise-type [op args cb]
  (cb {:type :element-wise
       :op op
       :dim-syms (:dim-syms (first args))
       :args args}))

(def-typed-inline disp-element [[:ndarray A]] cb
  (element-wise-type 'disp-value [A] cb))

(def-call-by-expr element-wise [context0 args cb2]
  (compile-exprs
   context0 (rest args)
   (fn [context cargs]
     (element-wise-type 
      (first args) cargs 
      (pass-on-context context cb2)))))

(def-typed-inline execute [[dont-care X]] cb
   (cb (make-full-array-loop X)))

;;;;;;;;;;;;;; Assigment

(defn make-assignment [storage elements]
  `(do
     ~@(map 
        (fn [i x]
          `(aset 
            ~(:data storage) 
            (add :long ~(:offset storage) ~i)
            ~x))
        (range (count elements))
        elements)))

(def-typed-inline assign-element [[dont-care A]
                                  [dont-care B]] cb
  (if (not (contains? A :storage))
    (compilation-error "Left-hand side " A " cannot be assigned")
    (cb
     (make-assignment
      (:storage A)
      (flat-vector B)))))

(defn perform-assignment [A B cb]
  (element-wise-type
   'assign-element [A B]
   (fn [x]
     (cb (make-full-array-loop x)))))


(def-typed-inline assign [[dont-care A] 
                          [dont-care B]] cb
  (perform-assignment A B cb))

(defn array-op-tester [args]
  (some array-like? args))

(defn element-wise-array-op [name]
  (add-typed-inline 
   name
   array-op-tester
   (fn [[& args] cb]
     (element-wise-type 
      name args cb))))

(element-wise-array-op 'typed*)
(element-wise-array-op 'typed+)
(element-wise-array-op 'typed-)

(def-typed-inline make-ndarray [[dont-care x]] cb
  (disp x)
  (let [dst (gensym)
        et (:elem-type x)]
    `(let [~dst (allocate-ndarray ~(:dim-syms x) ~et)]
       ~(make-ndarray-type 
         (:dim-count x) (:elem-type x) dst
         (fn [arr]
           (disp arr)
           (perform-assignment 
            arr x cb))))))
       

(defmethod make-clojure-data :disp-element [x] nil)

(defn ndarray-type [elem-type dim-count]
  {:type :ndarray :dim-count dim-count :elem-type elem-type})

(def ndarray-test-spec
  '{:type :ndarray, :dim-count 2, :elem-type {:type :double}, 
    :offset G__14085, :dim-syms [G__14089 G__14090], 
    :step-syms [G__14087 G__14088], :data G__14086, 
    :actual-steps [G__14091 G__14092]})
;(macroexpand '(statically (make-ndarray (input-value (ndarray-type {:type :double} 2)))))
