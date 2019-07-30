(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (= (str.tolower "aBCDef") x))
(assert (= x (str.++ y "c" z)))

(check-sat)
