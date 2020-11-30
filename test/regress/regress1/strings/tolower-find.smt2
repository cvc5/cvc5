(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)

(assert (= (str.tolower x) "abcde"))
(assert (= (str.tolower y) "abcde"))
(assert (not (= x "abcde")))
(assert (not (= y "abcde")))
(assert (not (= x y)))

(check-sat)
