(set-logic ALL)
(set-option :strings-exp true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)

(assert (= (str.to_lower x) "abcde"))
(assert (= (str.to_lower y) "abcde"))
(assert (not (= x "abcde")))
(assert (not (= y "abcde")))
(assert (not (= x y)))

(check-sat)
