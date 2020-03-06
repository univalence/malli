(ns malli.swagger
  (:require [malli.json-schema :as json-schema]
            [malli.core :as m]))

(defmulti accept (fn [name _schema _children _options] name) :default ::default)

(defmethod accept ::default [name schema children options] (json-schema/accept name schema children options))
(defmethod accept 'float? [_ _ _ _] {:type "number" :format "float"})
(defmethod accept 'double? [_ _ _ _] {:type "number" :format "double"})
(defmethod accept 'nil? [_ _ _ _] {})

(defmethod accept :and [_ _ children _] (assoc (first children) :x-allOf children))
(defmethod accept :or [_ _ children _] (assoc (first children) :x-anyOf children))
(defmethod accept :multi [_ _ children _] (let [cs (mapv last children)] (assoc (first cs) :x-anyOf cs)))

(defmethod accept :maybe [_ _ children {:keys [type in]}]
  (let [k (if (and (= type :parameter) (not= in :body)) :allowEmptyValue :x-nullable)]
    (assoc (first children) k true)))

(defmethod accept :tuple [_ _ children _] {:type "array" :items {} :x-items children})

(defn- -swagger-visitor [schema children _in options]
  (or (json-schema/maybe-prefix schema :swagger)
      (json-schema/maybe-prefix schema :json-schema)
      (merge (accept (m/name schema) schema children options)
             (json-schema/json-schema-props schema "swagger"))))

;;
;; public api
;;

(defn transform
  ([?schema]
   (transform ?schema nil))
  ([?schema options]
   (m/accept ?schema -swagger-visitor options)))
