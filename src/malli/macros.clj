(ns malli.macros
  (:refer-clojure :exclude [defn fn eval name])
  (:use malli.core)
  (:require [clojure.core :as c]))

(def ^:dynamic *debug* true)

(c/defn prob [& xs]
  (when *debug*
    (mapv clojure.pprint/pprint xs))
  (last xs))

(c/defn fm-args-syms []
  (map #(symbol (str "_fm-arg__" %)) (range)))

(c/defn- case-split [[v expr :as original-form]]

  (condp = v

    :else {:wild true :expr expr}
    :error {:error true :expr expr}

    (let [variadic? (= '& (first (take-last 3 v)))
          v (if-not variadic? v (concat (drop-last 3 v) (take-last 2 v)))
          pats (take-nth 2 v)
          arity (count pats)
          argv' (take (count pats) (fm-args-syms))
          schems (take-nth 2 (next v))
          conformer-syms (repeatedly (partial gensym "_fm-conformer__"))
          bindings (vec (interleave conformer-syms (map #(list `conformer %) schems)))
          form (reduce (c/fn [ret [pat argsym schem conformersym]]
                         `(when-let_c [~pat (~conformersym ~argsym) #_(and (~conformersym ~argsym) ~argsym)]
                                      ~ret
                                      #_(ex-info "bad argument " (explain ~schem ~argsym))))
                       {::return expr}
                       (reverse (map vector pats argv' schems conformer-syms)))]
      {:raw-form original-form
       :raw-pattern v
       :raw-expr expr
       :arity arity
       :variadic variadic?
       :bindings bindings
       :form form
       :argv argv'}
      )))


(defmacro fn [x & xs]

  (let [[nam [x & xs]] (if (symbol? x) [x xs] [(gensym) (cons x xs)])
        [return-spec clauses] (if (= :- x) [(first xs) (next xs)] [nil (cons x xs)])

        return-conformer-sym (gensym "_return-conformer__")

        wildcard? #{:else :error}

        pattern? #(or (vector %) (wildcard? %))

        clauses
        (cond

          ;; regular polyarity fn syntax: (pat1 & body1) (pat2 & body2) ...
          (every? seq? clauses)
          (map (c/fn [[p & bod :as all]]
                 (let [cnt (count bod)]
                   (if (= 1 cnt) all (list p (list* 'do bod))))
                 clauses))

          ;; match syntax: pat1 expr1 pat2 expr2 ...
          (every? pattern? (take-nth 2 clauses))
          (partition 2 clauses)

          ;; single arity: pattern & body
          (vector? (first clauses))
          (if (= 2 (count clauses))
            (list clauses)
            (list (list (first clauses) (list* 'do (next clauses))))))

        arg-syms (fm-args-syms)

        clauses (map case-split clauses)

        bindings (->> (mapcat :bindings clauses)
                      (concat [return-conformer-sym `(conformer ~return-spec)])
                      vec)

        wrap-return
        (c/fn [expr]
          (if return-spec
            `(or_c (~return-conformer-sym ~expr)
                   (ex-info "bad return " (explain ~return-spec ~expr)))
            expr))

        by-arity (->> clauses (remove :wild) (remove :error) (group-by :arity))

        wild-clause (:expr (first (filter :wild clauses)))
        error-clause (:expr (first (filter :error clauses)))

        expand-arity
        (c/fn [[n clauses]]
          (let [argv (vec (take n arg-syms))
                argv' (if (:variadic (first clauses))
                        (vec (concat (butlast argv) ['& (last argv)]))
                        argv)
                s (gensym "_arity-return__")]
            `(~argv' (if-let [~s (::return (or_c ~@(map :form clauses)))]
                       ~(wrap-return s)
                       ~(or error-clause
                            (and wild-clause (wrap-return wild-clause))
                            `(ex-info "no pattern for "
                                      {:args ~argv
                                       :patterns '~(map :raw-pattern clauses)}))))))]

    `(let ~bindings
       (c/fn ~nam ~@(mapv expand-arity by-arity)))))

(defmacro defn
  [name & clauses]
  `(def ~name (fn ~name ~@clauses)))


#_(macroexpand '(fn iop :- number? [a number?] a [a string?] (Integer/parseInt a)))
#_(let [f (fn iop :- number? [a number?] a [a string?] (Integer/parseInt a))]
    (f 1)
    (f "1")
    )

(let [f (fn iop :- number?
            [a number?] a
            [a string?] (Integer/parseInt a)
            [a number? & as [:sequential number?]] (reduce + a as)
            [a [:or number? string?]
             & as [:sequential [:or number? string?]]] (reduce + a (map iop as))
            ;:else 42
            :error (ex-info "arf" {:data :pata})
            )]
  (f 1)
  (f "1")
  (f 1 2 3)
  (f 1 "1" 2)
  (f 1 2 ::op)
  )