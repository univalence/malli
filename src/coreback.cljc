(ns malli.core
  (:refer-clojure :exclude [-name eval name])
  (:require [sci.core :as sci])
  #?(:clj (:import (java.util.regex Pattern))))

;;
;; protocols and records
;;

(defprotocol IntoSchema
  (-into-schema [this properties children options] "creates a new schema instance"))

(defprotocol Schema
  (-name [this] "returns name of the schema")
  (-conformer [this] "returns a predicate function that tries to conform the given value to the current schema")
  (-explainer [this path] "returns a function of `x in acc -> maybe errors` to explain the errors for invalid values")
  (-transformer [this transformer method options] "returns an interceptor map with :enter and :leave functions to transform the value for the given schema and method")
  (-accept [this visitor in options] "accepts the visitor to visit schema and it's children")
  (-properties [this] "returns original schema properties")
  (-options [this] "returns original options")
  (-form [this] "returns original form of the schema"))

(defprotocol Validator
  (-validator [this] "return a function that checks if the given value respects the current schema, returning a boolean"))

(extend-protocol Validator
  #?(:clj Object :cljs default)
  (-validator [this] (fn [x] (conform? (-conformer this)))))

(defprotocol MapSchema
  (-map-entries [this] "returns a predicate function that checks if the schema is valid"))

(defprotocol LensSchema
  (-get [this key default] "returns schema at key")
  (-set [this key value] "returns a copy with key having new value"))

(defprotocol Transformer
  (-transformer-chain [this] "returns transformer chain as a vector of maps with :name, :encoders, :decoders and :options")
  (-value-transformer [this schema method options] "returns an value transforming interceptor for the given schema and method"))

(defrecord SchemaError [path in schema value type message])

#?(:clj (defmethod print-method SchemaError [v ^java.io.Writer w]
          (.write w (str "#Error" (->> v (filter val) (into {}))))))

#?(:clj (defmethod print-method ::into-schema [v ^java.io.Writer w]
          (.write w (str "#IntoSchema{:class " v "}"))))

#?(:clj (defmethod print-method ::schema [v ^java.io.Writer w]
          (.write w (pr-str (-form v)))))

;;
;; impl
;;

(do :conformers-composition

    (def unconform ::unconform)
    (defn unconform? [x] (= x ::unconform))
    (defn conform? [x] (not= ::unconform x))

    (defmacro if_c [test then & [else]]
      `(if (conform? ~test) ~then ~(or else ::unconform)))

    (defmacro if-let_c [[pat expr] then & [else]]
      `(let [x# ~expr]
         (if (conform? x#)
           (let [~pat x#] ~then)
           ~(or else ::unconform))))

    (defmacro when_c [test & body]
      `(if_c ~test (do ~@body)))

    (defmacro when-let_c [binding & body]
      `(if-let_c ~binding (do ~@body)))

    (defmacro or_c
      ([] ::unconform)
      ([x & next] `(if-let_c [or# ~x] or# (or_c ~@next))))

    (defmacro and_c
      ([] true)
      ([x & next] `(when_c ~x (and_c ~@next))))

    (defn conformer-chain [conformers]
      (if-not (seq conformers)
        identity
        (fn [x]
          (loop [x x cs conformers]
            (if-not cs
              x (when-let_c [conformed ((first cs) x)]
                            (recur conformed (next cs))))))))

    (defn conformer-fork [conformers]
      (if-not (seq conformers)
        (constantly ::unconform)
        (fn [x]
          (loop [cs conformers]
            (if (seq cs)
              (if-let_c [conformed ((first cs) x)]
                        conformed
                        (recur (next cs)))
              ::unconform)))))
    )


(declare schema into-schema)
(declare eval)
(declare default-registry)

(defn keyword->string [x]
  (if (keyword? x)
    (if-let [nn (namespace x)]
      (str nn "/" (clojure.core/name x))
      (clojure.core/name x))
    x))

(defn error
  ([path in schema value]
   (->SchemaError path in schema value nil nil))
  ([path in schema value type]
   (->SchemaError path in schema value type nil)))

(defn error? [x]
  (instance? SchemaError x))

(defn fail!
  ([type]
   (fail! type nil))
  ([type data]
   (throw (ex-info (str type) {:type type, :data data}))))

(defn create-form [name properties children]
  (cond
    (and (seq properties) (seq children)) (into [name properties] children)
    (seq properties) [name properties]
    (seq children) (into [name] children)
    :else name))

(defn- -guard [pred tf]
  (if tf (fn [x] (if (pred x) (tf x) x))))

(defn- -predicate->conforming-fn [f]
  (fn [x]
    (if (f x) x ::unconform)))

(defn- -chain [phase chain]
  (when-let [fns (->> (case phase, :enter (rseq chain), :leave chain)
                      (keep identity)
                      (seq))]
    (apply comp fns)))

(defn- -leaf-schema [name ->conformer-and-children]
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (let [[conformer children] (->conformer-and-children properties children options)
            form (create-form name properties children)]
        ^{:type ::schema}
        (reify
          Schema
          (-name [_] name)
          (-conformer [_] conformer)
          (-explainer [this path]
            (fn [value in acc]
              (if-not (conform? (conformer value)) (conj acc (error path in this value)) acc)))
          (-transformer [this transformer method options]
            (-value-transformer transformer this method options))
          (-accept [this visitor in options]
            (visitor this (vec children) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form))))))

(defn fn-schema [name f]
  (-leaf-schema
    name
    (fn [properties children _]
      (when (seq children)
        (fail! ::child-error {:name name, :properties properties, :children children, :min 0, :max 0}))
      [f children])))

(defn- -partial-fn-schema [name f]
  (-leaf-schema
    name
    (fn [properties [child :as children] _]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name name, :properties properties, :children children, :min 1, :max 1}))
      [#(try (f % child) (catch #?(:clj Exception, :cljs js/Error) _ false)) children])))

(defn- -predicate-schema [name f]
  (-leaf-schema
    name
    (fn [properties children _]
      (when (seq children)
        (fail! ::child-error {:name name, :properties properties, :children children, :min 0, :max 0}))
      [(-predicate->conforming-fn f) children])))

(defn- -partial-predicate-schema [name f]
  (let [cfn (-predicate->conforming-fn f)]
    (-leaf-schema
      name
      (fn [properties children _]
        (when-not (pos? (count children))
          (fail! ::child-error {:name name, :properties properties, :children children, :min 1}))
        [#(apply cfn % children) children]))))

(defn -composite-schema [{:keys [name compose short-circuit shrink]}]
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      #_(when-not (seq children)
          (fail! ::no-children {:name name, :properties properties}))
      (let [child-schemas (mapv #(schema % options) children)
            validators (map -conformer child-schemas)
            validators (if shrink (distinct validators) validators)
            validator (compose validators)
            distance (if (seq properties) 2 1)]
        ^{:type ::schema}
        (reify Schema
          (-name [_] name)
          (-conformer [_] validator)
          (-explainer [_ path]
            (let [explainers (mapv (fn [[i c]] (-explainer c (into path [(+ i distance)]))) (map-indexed vector child-schemas))]
              (fn explain [x in acc]
                (reduce
                  (fn [acc' explainer]
                    (let [acc'' (explainer x in acc')]
                      (cond
                        (and short-circuit (identical? acc' acc'')) (reduced acc)
                        (nil? acc'') acc'
                        :else acc'')))
                  acc explainers))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  child-transformers (map #(-transformer % transformer method options) child-schemas)
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ?->this (or ->this identity)
                                ->children (into [] (keep phase) child-transformers)]
                            (cond
                              (not (seq ->children)) ->this
                              short-circuit (fn [x]
                                              (let [x (?->this x)]
                                                (reduce-kv
                                                  (fn [_ _ t]
                                                    (let [x' (t x)]
                                                      (if-not (identical? x' x)
                                                        (reduced x')
                                                        x)))
                                                  x ->children)))
                              :else (fn [x]
                                      (reduce-kv
                                        (fn [x' _ t] (t x'))
                                        (?->this x) ->children)))))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this (mapv #(-accept % visitor in options) child-schemas) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] (create-form name properties (map -form child-schemas)))
          LensSchema
          (-get [_ key default] (get child-schemas key default))
          (-set [_ key value] (into-schema name properties (assoc child-schemas key value))))))))

(def -and-schema
  (-composite-schema
    {:name :and
     :compose conformer-chain
     :short-circuit false
     :shrink true}))

(def -or-schema
  (-composite-schema
    {:name :or
     :compose conformer-fork
     :short-circuit true
     :shrink true}))

(comment
  (conform nil? nil)
  (assert (nil? (conform [:or number? nil?] nil))))

(defn- -properties-and-children [xs]
  (if ((some-fn map? nil?) (first xs))
    [(first xs) (rest xs)]
    [nil xs]))

(defn- -expand-key [[k ?p ?v] options f]
  (let [[p v] (if (or (nil? ?p) (map? ?p)) [?p ?v] [nil ?p])]
    [k p (f (schema v options))]))

(defn- -parse-map-entries [children options]
  (->> children (mapv #(-expand-key % options identity))))

(defn ^:no-doc map-entry-forms [entries]
  (mapv (fn [[k p v]] (let [v' (-form v)] (if p [k p v'] [k v']))) entries))

(defn ^:no-doc required-map-entry? [[_ ?p]]
  (not (and (map? ?p) (true? (:optional ?p)))))

(defn- -map-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ {:keys [closed] :as properties} children options]
      (let [entries (-parse-map-entries children options)
            keyset (->> entries (map first) (set))
            forms (map-entry-forms entries)
            form (create-form :map properties forms)
            distance (if (seq properties) 2 1)]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_]
            (let [validators
                  (cond-> (mapv
                            (fn [[key {:keys [optional]} value]]
                              (let [valid? (-conformer value)
                                    default (boolean optional)]
                                (fn [m] (if-let [map-entry (find m key)] (valid? (val map-entry)) default))))
                            entries)
                          closed (into [(fn [m]
                                          (reduce
                                            (fn [acc k] (if (contains? keyset k) acc (reduced false)))
                                            true (keys m)))]))
                  check
                  (fn [m]
                    (boolean
                      #?(:clj  (let [it (.iterator ^Iterable validators)]
                                 (boolean
                                   (loop []
                                     (if (.hasNext it)
                                       (and ((.next it) m) (recur))
                                       true))))
                         :cljs (reduce #(or (%2 m) (reduced false)) true validators))))]
              (fn [m] (and (map? m) (check m)))))
          Schema
          (-name [_] :map)
          (-conformer [_]
            (let [validators2
                  (cond-> (mapv
                            (fn [[key {:keys [optional]} value]]
                              (let [cfn (-conformer value)
                                    default (boolean optional)]
                                (fn [m] (if-let [map-entry (find m key)]
                                          (when-let_c [v' (cfn (val map-entry))]
                                                      (assoc m key v'))
                                          default))))
                            entries)

                          closed
                          (into [(fn [m]
                                   (when_c (reduce
                                             (fn [acc k] (if (contains? keyset k) acc (reduced ::unconform)))
                                             true (keys m))
                                           m))]))

                  conform
                  (fn [m]
                    (loop [ret m vs validators2]
                      (if-not vs
                        ret
                        (when-let [m' ((first vs) m)] (recur m' (next vs))))))]

              (fn [m] (and (map? m) (conform m) #_(validate m)))))

          (-explainer [this path]
            (let [explainers (cond-> (mapv
                                       (fn [[i [key {:keys [optional] :as key-properties} schema]]]
                                         (let [key-distance (if (seq key-properties) 2 1)
                                               explainer (-explainer schema (into path [(+ i distance) key-distance]))
                                               key-path (into path [(+ i distance) 0])]
                                           (fn [x in acc]
                                             (if-let [e (find x key)]
                                               (explainer (val e) (conj in key) acc)
                                               (if-not optional
                                                 (conj acc (error key-path (conj in key) this nil ::missing-key))
                                                 acc)))))
                                       (map-indexed vector entries))
                                     closed (into [(fn [x in acc]
                                                     (reduce
                                                       (fn [acc k]
                                                         (if (contains? keyset k)
                                                           acc
                                                           (conj acc (error path (conj in k) this nil ::extra-key))))
                                                       acc (keys x)))]))]
              (fn [x in acc]
                (if-not (map? x)
                  (conj acc (error path in this x ::invalid-type))
                  (reduce
                    (fn [acc explainer]
                      (explainer x in acc))
                    acc explainers)))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  transformers (some->>
                                 entries
                                 (keep (fn [[k _ s]] (if-let [t (-transformer s transformer method options)] [k t])))
                                 (into {}))
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ->children (->> transformers
                                                (keep (fn extract-value-transformer-phase [[k t]]
                                                        (if-let [phase-t (phase t)]
                                                          [k phase-t])))
                                                (into {}))
                                apply->children (if (seq ->children)
                                                  #(reduce-kv
                                                     (fn reduce-child-transformers [m k t]
                                                       (if-let [entry (find m k)]
                                                         (assoc m k (t (val entry)))
                                                         m))
                                                     % ->children))]
                            (-chain phase [->this (-guard map? apply->children)])))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this (mapv (fn [[k p s]] [k p (-accept s visitor (conj in k) options)]) entries) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form)
          MapSchema
          (-map-entries [_] entries)
          LensSchema
          (-get [_ key default] (or (some (fn [[k _ s]] (if (= k key) s)) entries) default))
          (-set [_ key value]
            (let [found (atom nil)
                  [key kprop] (if (vector? key) key [key])
                  entries (cond-> (mapv (fn [[k p s]] (if (= key k) (do (reset! found true) [k kprop value]) [k p s])) entries)
                                  (not @found) (conj [key kprop value])
                                  :always (->> (filter (fn [e] (-> e last some?)))))]
              (into-schema :map properties entries))))))))

(defn- -map-of-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (when-not (and (seq children) (= 2 (count children)))
        (fail! ::child-error {:name :vector, :properties properties, :children children, :min 2, :max 2}))
      (let [[key-schema value-schema :as schemas] (mapv #(schema % options) children)
            key-valid? (-conformer key-schema)
            value-valid? (-conformer value-schema)
            validate (fn [m]
                       (reduce-kv
                         (fn [_ key value]
                           (or (and (key-valid? key) (value-valid? value)) (reduced false)))
                         true m))
            conform (fn [m]
                      (reduce-kv
                        (fn [acc key value]
                          (when-let_c
                            [k (key-valid? key)]
                            (when-let_c
                              [v (value-valid? value)]
                              (assoc acc k v)))
                          (or (and (key-valid? key) (value-valid? value)) (reduced false)))
                        {} m))
            distance (if (seq properties) 2 1)]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_] (fn [m] (and (map? m) (validate m))))
          Schema
          (-name [_] :map-of)
          (-conformer [_] (fn [m] (and (map? m) (conform m))))
          (-explainer [this path]
            (let [key-explainer (-explainer key-schema (conj path distance))
                  value-explainer (-explainer value-schema (conj path (inc distance)))]
              (fn explain [m in acc]
                (if-not (map? m)
                  (conj acc (error path in this m ::invalid-type))
                  (reduce-kv
                    (fn [acc key value]
                      (let [in (conj in key)]
                        (->> acc
                             (key-explainer key in)
                             (value-explainer value in))))
                    acc m)))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  key-transformer (-transformer key-schema transformer method options)
                  child-transformer (-transformer value-schema transformer method options)
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ->key (if-let [t (phase key-transformer)]
                                        (fn [x] (t x)))
                                ->child (phase child-transformer)
                                ->key-child (cond
                                              (and ->key ->child) #(assoc %1 (->key %2) (->child %3))
                                              ->key #(assoc %1 (->key %2) %3)
                                              ->child #(assoc %1 %2 (->child %3)))
                                apply->key-child (if ->key-child #(reduce-kv ->key-child (empty %) %))]
                            (-chain phase [->this (-guard map? apply->key-child)])))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this (mapv #(-accept % visitor in options) schemas) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] (create-form :map-of properties (mapv -form schemas))))))))

(defn- -collection-schema [name fpred fwrap fempty]
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ {:keys [min max] :as properties} children options]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name name, :properties properties, :children children, :min 1, :max 1}))
      (let [schema (schema (first children) options)
            form (create-form name properties [(-form schema)])
            fwrap (fn [x]
                    (if (coll? x)
                      (fwrap x)
                      x))
            validate-limits (cond
                              (not (or min max)) (constantly true)
                              (and min max) (fn [x] (let [size (count x)] (<= min size max)))
                              min (fn [x] (let [size (count x)] (<= min size)))
                              max (fn [x] (let [size (count x)] (<= size max))))
            distance (if (seq properties) 2 1)]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_]
            (let [validator (-validator schema)]
              (fn [x] (and (fpred x)
                           (validate-limits x)
                           (reduce (fn [acc v] (if (validator v) acc (reduced false))) true x)))))
          Schema
          (-name [_] name)
          (-conformer [_]
            (let [cfn (-conformer schema)]
              (fn [c]
                (and (fpred c)
                     (validate-limits c)
                     (when-let_c
                       [ret (loop [ret [] xs (seq c)]
                              (if-not xs
                                ret (when-let_c [x (cfn (first xs))]
                                                (recur (conj ret x) (next xs)))))]
                       (fwrap ret))))))
          (-explainer [this path]
            (let [explainer (-explainer schema (conj path distance))]
              (fn [x in acc]
                (cond
                  (not (fpred x)) (conj acc (error path in this x ::invalid-type))
                  (not (validate-limits x)) (conj acc (error path in this x ::limits))
                  :else (let [size (count x)]
                          (loop [acc acc, i 0, [x & xs] x]
                            (if (< i size)
                              (cond-> (or (explainer x (conj in i) acc) acc) xs (recur (inc i) xs))
                              acc)))))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  child-transformer (-transformer schema transformer method options)
                  build (fn [phase]
                          (let [->this (or (phase this-transformer) fwrap)
                                ->child (if-let [ct (phase child-transformer)]
                                          (if fempty
                                            #(into (if % fempty) (map ct) %)
                                            #(map ct %)))]
                            (-chain phase [->this (-guard coll? ->child)])))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this [(-accept schema visitor (conj in ::in) options)] in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form)
          LensSchema
          (-get [_ key default] (if (= 0 key) schema default))
          (-set [_ key value] (if (= 0 key) (into-schema name properties [value]) schema)))))))

(defn- -tuple-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (let [schemas (mapv #(schema % options) children)
            size (count schemas)
            form (create-form :tuple properties (map -form schemas))
            validators (into (array-map) (map-indexed vector (mapv -conformer schemas)))
            distance (if (seq properties) 2 1)]
        (when-not (seq children)
          (fail! ::child-error {:name :tuple, :properties properties, :children children, :min 1}))
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_]
            (fn [x] (and (vector? x)
                         (= (count x) size)
                         (reduce-kv
                           (fn [acc i validator]
                             (if (validator (nth x i)) acc (reduced false))) true validators))))
          Schema
          (-name [_] :tuple)
          (-conformer [_]
            (fn [x] (and (vector? x)
                         (= (count x) size)
                         (loop [x x vs (seq validators)]
                           (if-not vs
                             x (let [v (first vs) i (key v)]
                                 (when-let_c [conformed ((val v) (get x i))]
                                             (recur (assoc x i conformed) (next vs)))))))))
          (-explainer [this path]
            (let [
                  explainers (mapv (fn [[i s]]
                                     (-explainer s (conj path (+ i distance))))
                                   (map-indexed vector schemas))]
              (fn [x in acc]
                (cond
                  (not (vector? x)) (conj acc (error path in this x ::invalid-type))
                  (not= (count x) size) (conj acc (error path in this x ::tuple-size))
                  :else (loop [acc acc, i 0, [x & xs] x, [e & es] explainers]
                          (cond-> (e x (conj in i) acc) xs (recur (inc i) xs es)))))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  child-transformers (->> schemas
                                          (mapv #(-transformer % transformer method options))
                                          (map-indexed vector)
                                          (into {}))
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ->children (->> child-transformers
                                                (keep (fn [[k t]] (if-let [t (phase t)] [k t])))
                                                (into {}))
                                apply->children #(reduce-kv update % ->children)]
                            (-chain phase [->this (-guard vector? apply->children)])))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this (mapv
                            (fn [[i s]] (-accept s visitor (conj in i) options))
                            (map-indexed vector schemas)) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form #_(create-form :tuple properties (map -form schemas)) #_form)
          LensSchema
          (-get [_ key default] (get schemas key default))
          (-set [_ key value] (into-schema :tuple properties (assoc schemas key value))))))))

(defn- -enum-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (when-not (seq children)
        (fail! ::no-children {:name :enum, :properties properties}))
      (let [schema (set children)
            validator (fn [x] (contains? schema x))]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_] validator)
          Schema
          (-name [_] :enum)
          (-conformer [_] schema)
          (-explainer [this path]
            (fn explain [x in acc]
              (if-not (validator x) (conj acc (error path in this x)) acc)))
          ;; TODO: should we try to derive the type from values? e.g. [:enum 1 2] ~> int?
          (-transformer [this transformer method options]
            (-value-transformer transformer this method options))
          (-accept [this visitor in options]
            (visitor this (vec children) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] (create-form :enum properties children)))))))

(defn- -re-schema [class?]
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties [child :as children] options]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name :re, :properties properties, :children children, :min 1, :max 1}))
      (let [re (re-pattern child)
            validator (fn [x] (try (boolean (re-find re x)) (catch #?(:clj Exception, :cljs js/Error) _ false)))
            conformer (-predicate->conforming-fn validator)
            form (if class? re (create-form :re properties children))]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_] validator)
          Schema
          (-name [_] :re)
          (-conformer [_] conformer)
          (-explainer [this path]
            (fn explain [x in acc]
              (try
                (if-not (re-find re x)
                  (conj acc (error path in this x))
                  acc)
                (catch #?(:clj Exception, :cljs js/Error) e
                  (conj acc (error path in this x (:type (ex-data e))))))))
          (-transformer [this transformer method options]
            (-value-transformer transformer this method options))
          (-accept [this visitor in options]
            (visitor this (vec children) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form))))))

(defn- -fn-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name :fn, :properties properties, :children children, :min 1, :max 1}))
      (let [f (eval (first children))
            validator (fn [x] (try (f x) (catch #?(:clj Exception, :cljs js/Error) _ false)))
            conformer (fn [x] (try (f x) (catch #?(:clj Exception, :cljs js/Error) _ ::unconform)))]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_] validator)
          Schema
          (-name [_] :fn)
          (-conformer [_] conformer)
          (-explainer [this path]
            (fn explain [x in acc]
              (try
                (if-not (f x)
                  (conj acc (error path in this x))
                  acc)
                (catch #?(:clj Exception, :cljs js/Error) e
                  (conj acc (error path in this x (:type (ex-data e))))))))
          (-transformer [this transformer method options]
            (-value-transformer transformer this method options))
          (-accept [this visitor in options]
            (visitor this (vec children) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] (create-form :fn properties children)))))))

(defn- -maybe-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name :vector, :properties properties, :children children, :min 1, :max 1}))
      (let [schema' (-> children first (schema options))
            conformer (-conformer schema')
            validator (-validator schema')
            form (create-form :maybe properties [(-form schema')])]
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_] (fn [x] (or (nil? x) (validator x))))
          Schema
          (-name [_] :maybe)
          (-conformer [_] (fn [x] (or_c (nil? x) (conformer x))))
          (-explainer [this path]
            (fn explain [x in acc]
              (if-not (or (nil? x) (validator x)) (conj acc (error path in this x)) acc)))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  child-transformer (-transformer schema' transformer method options)
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ->child (phase child-transformer)]
                            (if (and ->this ->child)
                              (comp ->child ->this)
                              (or ->this ->child))))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this [(-accept schema' visitor in options)] in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form)
          LensSchema
          (-get [_ key default] (if (= 0 key) schema' default))
          (-set [_ key value] (if (= 0 key) (into-schema :maybe properties [value]) schema')))))))

(defn- -multi-schema []
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (let [entries (-parse-map-entries children options)
            forms (map-entry-forms entries)
            dispatch (eval (:dispatch properties))
            dispatch-map (->> (for [[d _ s] entries] [d s]) (into {}))
            form (create-form :multi properties forms)
            distance (if properties 2 1)]
        (when-not dispatch
          (fail! ::missing-property {:key :dispatch}))
        ^{:type ::schema}
        (reify
          Validator
          (-validator [_]
            (let [validators (reduce-kv (fn [acc k s] (assoc acc k (-conformer s))) {} dispatch-map)]
              (fn [x]
                (if-let [validator (validators (dispatch x))]
                  (validator x)
                  false))))
          Schema
          (-name [_] :multi)
          (-conformer [_]
            (let [conformers (reduce-kv (fn [acc k s] (assoc acc k (-conformer s))) {} dispatch-map)]
              (fn [x]
                (when-let_c
                  [conformer (conformers (dispatch x))]
                  (conformer x)))))
          (-explainer [this path]
            (let [explainers (reduce
                               (fn [acc [i [key key-properties schema]]]
                                 (let [key-distance (if (seq key-properties) 2 1)
                                       explainer (-explainer schema (into path [(+ i distance) key-distance]))]
                                   (assoc acc key (fn [x in acc] (explainer x in acc)))))
                               {} (map-indexed vector entries))]
              (fn [x in acc]
                (if-let [explainer (explainers (dispatch x))]
                  (explainer x in acc)
                  (conj acc (error path in this x ::invalid-dispatch-value))))))
          (-transformer [this transformer method options]
            (let [this-transformer (-value-transformer transformer this method options)
                  child-transformers (reduce-kv
                                       #(assoc %1 %2 (-transformer %3 transformer method options))
                                       {} dispatch-map)
                  build (fn [phase]
                          (let [->this (phase this-transformer)
                                ->children (->> child-transformers
                                                (keep (fn [[k v]] (if-let [t (phase v)] [k t])))
                                                (into {}))
                                ->child (if (seq ->children) (fn [x] (if-let [t (->children (dispatch x))] (t x) x)))]
                            (-chain phase [->this ->child])))]
              {:enter (build :enter)
               :leave (build :leave)}))
          (-accept [this visitor in options]
            (visitor this (mapv (fn [[k p s]] [k p (-accept s visitor in options)]) entries) in options))
          (-properties [_] properties)
          (-options [_] options)
          (-form [_] form))))))

(defn- -register [registry k schema]
  (if (contains? registry k)
    (fail! ::schema-already-registered {:key k, :registry registry}))
  (assoc registry k schema))

(defn- -register-predicate-var [registry v]
  (let [name (-> v meta :name)
        schema (-predicate-schema name @v)]
    (-> registry
        (-register name schema)
        (-register @v schema))))

(defn- -schema [?schema {:keys [registry schemas] :as options :or {registry default-registry}}]
  (let [registry (merge registry schemas)]
    (or (if (satisfies? IntoSchema ?schema) ?schema)
        (get registry ?schema)
        (some-> registry (get (type ?schema)) (-into-schema nil [?schema] options)))))

(defn ^:no-doc into-transformer [x]
  (cond
    (satisfies? Transformer x) x
    (fn? x) (into-transformer (x))
    :else (fail! ::invalid-transformer {:value x})))

;;
;; public api
;;

(do

  (defn into-schema
    ([name properties children]
     (into-schema name properties children nil))
    ([name properties children options]
     (-into-schema (-schema name options) (if (seq properties) properties) children options)))

  (defn schema? [x]
    (satisfies? Schema x))

  (defn schema
    ([?schema]
     (schema ?schema nil))
    ([?schema options]
     ;; TODO do we want to allow value value schemas, I mean 42 could be a schema that matches 42 only ?
     (cond
       (schema? ?schema) ?schema
       (satisfies? IntoSchema ?schema) (-into-schema ?schema nil nil options)
       (vector? ?schema) (apply into-schema (concat [(-schema (first ?schema) options)]
                                                    (-properties-and-children (rest ?schema)) [options]))
       :else (or (some-> ?schema (-schema options) (schema options)) (fail! ::invalid-schema {:schema ?schema})))))

  (defn form
    ([?schema]
     (form ?schema nil))
    ([?schema options]
     (-form (schema ?schema options))))

  (defn accept
    ([?schema visitor]
     (accept ?schema visitor nil))
    ([?schema visitor options]
     (-accept (schema ?schema options) visitor [] options)))

  (defn properties
    ([?schema]
     (properties ?schema nil))
    ([?schema options]
     (-properties (schema ?schema options))))

  (defn options
    ([?schema]
     (options ?schema nil))
    ([?schema options]
     (-options (schema ?schema options))))

  (defn children
    ([?schema]
     (children ?schema nil))
    ([?schema options]
     (let [schema (schema ?schema options)
           form (-form schema)]
       (if (vector? form)
         (->> form (drop (if (seq (-properties schema)) 2 1)))))))

  (defn name
    ([?schema]
     (name ?schema nil))
    ([?schema options]
     (-name (schema ?schema options))))

  (defn conformer
    ([?schema]
     (conformer ?schema nil))
    ([?schema options]
     (-conformer (schema ?schema options))))

  (defn conform
    ([?schema value]
     (conform ?schema value nil))
    ([?schema value options]
     ((conformer ?schema options) value)))

  (defn validator
    ([?schema]
     (validator ?schema nil))
    ([?schema options]
     (-validator (schema ?schema options))))

  (defn validate
    ([?schema value]
     (validate ?schema value nil))
    ([?schema value options]
     ((validator ?schema options) value)))

  (defn explainer
    ([?schema]
     (explainer ?schema nil))
    ([?schema options]
     (let [schema' (schema ?schema options)
           explainer' (-explainer schema' [])]
       (fn explainer
         ([value]
          (explainer value [] []))
         ([value in acc]
          (if-let [errors (seq (explainer' value in acc))]
            {:schema schema'
             :value value
             :errors errors}))))))

  (defn explain
    ([?schema value]
     (explain ?schema value nil))
    ([?schema value options]
     ((explainer ?schema options) value [] [])))

  (defn decoder
    "Creates a value decoding transformer given a transformer and a schema."
    ([?schema t]
     (decoder ?schema nil t))
    ([?schema options t]
     (let [{:keys [enter leave]} (-transformer (schema ?schema options) (into-transformer t) :decode options)]
       (cond
         (and enter leave) (comp leave enter)
         (or enter leave) (or enter leave)
         :else identity))))

  (defn decode
    "Transforms a value with a given decoding transformer against a schema."
    ([?schema value t]
     (decode ?schema value nil t))
    ([?schema value options t]
     (if-let [transform (decoder ?schema options t)]
       (transform value)
       value)))

  (defn encoder
    "Creates a value encoding transformer given a transformer and a schema."
    ([?schema t]
     (encoder ?schema nil t))
    ([?schema options t]
     (let [{:keys [enter leave]} (-transformer (schema ?schema options) (into-transformer t) :encode options)]
       (cond
         (and enter leave) (comp leave enter)
         (or enter leave) (or enter leave)
         :else identity))))

  (defn encode
    "Transforms a value with a given encoding transformer against a schema."
    ([?schema value t]
     (encode ?schema value nil t))
    ([?schema value options t]
     (if-let [transform (encoder ?schema options t)]
       (transform value)
       value)))

  (defn map-entries
    "Returns a sequence of 3-element map-entry tuples of type `key ?properties schema`"
    ([?schema]
     (map-entries ?schema nil))
    ([?schema options]
     (if-let [schema (schema ?schema options)]
       (if (satisfies? MapSchema schema)
         (-map-entries schema)))))

  (defn ^:no-doc eval [?code]
    (if (fn? ?code) ?code (sci/eval-string (str ?code) {:preset :termination-safe
                                                        :bindings {'m/properties properties
                                                                   'm/name name
                                                                   'm/children children
                                                                   'm/map-entries map-entries}}))))
;;
;; Visitors
;;

(defn schema-visitor [f]
  (fn [schema children _ options]
    (f (into-schema (name schema) (properties schema) children options))))

(defn ^:no-doc map-syntax-visitor [schema children _ _]
  (let [properties (properties schema)]
    (cond-> {:name (name schema)}
            (seq properties) (assoc :properties properties)
            (seq children) (assoc :children children))))

;;
;; registries
;;

(def predicate-registry
  (->> [#'any? #'some? #'number? #'integer? #'int? #'pos-int? #'neg-int? #'nat-int? #'float? #'double?
        #'boolean? #'string? #'ident? #'simple-ident? #'qualified-ident? #'keyword? #'simple-keyword?
        #'qualified-keyword? #'symbol? #'simple-symbol? #'qualified-symbol? #'uuid? #'uri? #?(:clj #'decimal?)
        #'inst? #'seqable? #'indexed? #'map? #'vector? #'list? #'seq? #'char? #'set? #'nil? #'false? #'true?
        #'zero? #?(:clj #'rational?) #'coll? #'empty? #'associative? #'sequential? #?(:clj #'ratio?) #?(:clj #'bytes?)]
       (reduce -register-predicate-var {})))

(def class-registry
  {#?(:clj Pattern, :cljs js/RegExp) (-re-schema true)})

(def comparator-registry
  (->> {:> >, :>= >=, :< <, :<= <=, := =, :not= not=}
       (map (fn [[k v]] [k (-partial-fn-schema k v)]))
       (into {})
       (reduce-kv -register nil)))

(def base-registry
  {:and -and-schema #_(-composite-schema {:name :and :compose every-pred :short-circuit false :shrink true})
   :or -or-schema #_(-composite-schema {:name :or :compose some-fn :short-circuit true :shrink true})
   :map (-map-schema)
   :map-of (-map-of-schema)
   :vector (-collection-schema :vector vector? vec [])
   :list (-collection-schema :list list? seq nil)
   :sequential (-collection-schema :sequential sequential? seq nil)
   :set (-collection-schema :set set? set #{})
   :enum (-enum-schema)
   :maybe (-maybe-schema)
   :tuple (-tuple-schema)
   :multi (-multi-schema)
   :re (-re-schema false)
   :fn (-fn-schema)})

;; tweak s

(defn- -raw-fn-schema [name guard?]
  ^{:type ::into-schema}
  (reify IntoSchema
    (-into-schema [_ properties children options]
      (if (> (count children) 1)
        (schema (into [:>>] (map vector (repeat name) children)))
        (let [f (first children)
              f (if guard? (fn [x] (when (f x) x)) f)]
          ^{:type ::schema}
          (reify Schema
            (-name [_] name)
            (-conformer [_] f)
            (-explainer [this path]
              (fn explain [x in acc]
                (try
                  (if-not (f x)
                    (conj acc (error path in this x))
                    acc)
                  (catch #?(:clj Exception, :cljs js/Error) e
                    (conj acc (error path in this x (:type (ex-data e))))))))
            (-transformer [this transformer method options]
              (-value-transformer transformer this method options))
            (-accept [this visitor in options] (visitor this (vec children) in options))
            (-properties [_] properties)
            (-options [_] options)
            (-form [_] (create-form name properties children))))))))

(defn -lazy-schema []
  (reify IntoSchema
    (-into-schema [_ _ children options]
      (when-not (= 1 (count children))
        (fail! ::child-error {:name :fn, :properties properties, :children children, :min 1, :max 1}))
      (let [schem* (atom nil)
            validator* (atom nil)
            conformer* (atom nil)
            explainer* (atom nil)
            get-schema (fn [] (when (not @schem*) (reset! schem* (schema (first children) options))) @schem*)
            get-conformer (fn [] (when (not @conformer*) (reset! conformer* (conformer (get-schema) options))) @conformer*)
            get-validator (fn [] (when (not @validator*) (reset! validator* (validator (get-schema) options))) @validator*)
            get-explainer (fn [] (when (not @explainer*) (reset! explainer* (explainer (get-schema) options))) @explainer*)]
        (reify
          Validator
          (-validator [_] (fn [x] ((get-validator) x)))
          Schema
          (-name [_] (-name (get-schema)))
          (-conformer [_] (fn [x] ((get-conformer) x)))
          (-explainer [_ path] (fn [x in acc] ((get-explainer) x in acc)))
          (-transformer [_ transformer method options]
            (let [transformer (fn [] (-transformer (get-schema) transformer method options))]
              {:enter (fn [x] ((:enter (transformer)) x))
               :leave (fn [x] ((:leave (transformer)) x))}))
          (-accept [_ visitor in options] (-accept (get-schema) visitor in options))
          (-properties [_] (-properties (get-schema)))
          (-options [_] (-options (get-schema)))
          (-form [this] [:lazy (first children)]))))))

(def -threading-schema
  (-composite-schema
    {:name :>>
     :compose
     (fn [conformers]
       (letfn [(loop [x cs]
                 (if (not (seq cs))
                   x (when-let_c [x' ((first cs) x)]
                                 (loop x' (next cs)))))]
         (fn [x] (loop x conformers))))
     :short-circuit false
     :shrink false}))

(def extra-registry

  {:f (-raw-fn-schema :f false)
   :g (-raw-fn-schema :g true)
   :>> -threading-schema
   :lazy (-lazy-schema)})

(def default-registry
  (clojure.core/merge
    predicate-registry class-registry
    comparator-registry base-registry extra-registry))

(do

  (defn conform! [s x & [options]]
    (assert (= x (conform s x options))))

  (defn unconform! [s x]
    (assert (unconform? (conform s x))))

  ;;
  (conform! number? 1)
  (unconform! number? :1)

  (conform! nil? nil)
  (unconform! nil? 1)

  (conform! false? false)
  (unconform! false? nil)

  (conform! any? nil)
  (conform! any? 1)

  (conform! [:or number? string?] 1)
  (conform! [:or number? nil?] nil)
  (conform! [:or number? string?] "aze")
  (unconform! [:or number? string?] :op)

  (conform! [:and number? pos-int?] 1)
  (unconform! [:and number? pos-int?] -1)

  (conform! [:tuple number? nil?] [1 nil])



  (explain [:tuple any? any? [:vector string?]] [9 12 ["a" "b" 2]])

  (conform! [:map [:a number?] [:b string?]]
            {:a 1 :b "io"})

  (unconform! [:map [:a number?] [:b string?]]
              {:a 1 :b 2})

  (unconform! [:map {:closed true} [:a number?] [:b string?]]
              {:a 1 :b "a" :c 3})

  ;; recursion
  (conform!
    :cons
    [1 [2 [3 nil]]]
    {:schemas {:cons [:or nil? [:tuple any? [:lazy :cons]]]}}))



(comment

  (clojure.pprint/pprint predicate-registry)

  (defmacro bench [e & {:as options}]
    `(let [start# (System/currentTimeMillis)
           _# (dotimes [~'_ ~(:n options 1000000)] ~e)
           done# (System/currentTimeMillis)]
       {'~(:name options e) (- done# start#)}))

  (let [v (conformer [:map {:closed true} [:a number?] [:b string?]])]
    (bench (v {:a 1 :b "a" :c 3})))

  (let [v (-validator (schema [:map {:closed true} [:a number?] [:b string?]]))]
    (bench (v {:a 1 :b "a" :c 3}))))