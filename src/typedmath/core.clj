(ns typedmath.core)

;; Represents any number on the host platform.
(defn make-number [x]
  (assert (number? x))
  {:type :number :value x})

;; Represents something not known at compile time.
(defn make-dynamic [x]
  {:type :dynamic :value x})

(defn conj-in-map [m key value]
  (if (contains? m key)
    (update-in m [key] #(conj % value))
    (assoc m key [value])))

(assert (= {:katt [119]} (conj-in-map {} :katt 119)))
(assert (= {:katt [119 120]} 
           (conj-in-map {:katt [119]} :katt 120)))
               
;; A look-up table of defined functions
(let [table (atom {})]
  (defn add-inline-function [name tester? fun]
    (swap! table #(conj-in-map % name [tester? fun])))

  (defn find-inline-function [name args]
    (if-let [[tester? fun]
             (first
              (filter 
               (fn [[tester? fun]]
                 (if (tester? args) fun))
               (get (deref table) name)))]
             fun)))

(add-inline-function 'dummy 
                     (fn [args]
                       (every? number? args))
                     :dummy-numbers)

(assert (= :dummy-numbers
           (find-inline-function 'dummy [1 2 3])))
(assert (nil? (find-inline-function 'another-dummy [1 2 3])))

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

(defmacro defn-typed [name types cb & body]
  (assert (symbol? name))
  (assert (valid-type-spec? types))
  (assert (symbol? cb))
  `(add-inline-function 
    (quote ~name)
    (make-type-tester (quote ~types))
    (fn [[~@(map second types)] ~cb]
      ~@body)))

(defn-typed typed+ [[:number a] [:number b]] cb
  (cb {:type :number
       :expr 119})); `(+ ~(:expr a) ~(:expr b))}))

(assert (= {:type :number :value 9}) (make-number 9))

(declare compile-form)

(defn compile-exprs-sub [args acc cb]
  (if (empty? args)
    (cb acc)
    (compile-form 
     (first args)
     (fn [arg]
       (compile-exprs-sub (rest args) (conj acc arg) cb)))))

;; Used to compile a sequence of exprs. The compiled
;; exprs are passed as a vector to the callback cb.
(defn compile-exprs [exprs cb]
  (compile-exprs-sub exprs [] cb))

(assert (= [{:type :number :value 9} {:type :number :value 11}])
        (compile-exprs [9 11] identity))

(defn compile-form [x cb]
  (cond
    (number? x) (cb (make-number x))
    (symbol? x) (cb (make-dynamic x))
    :default "Failed"))

(assert [:this-is-a-number {:type :number :value 9}]
        (compile-form 9 (fn [x] [:this-is-a-number x])))



;(defn compile-forms [frms]
;  (

;(defmacro statically [& frms]
;  (compile-forms frms))
