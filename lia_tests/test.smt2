(set-logic ALL)

(declare-const a Bool)
(assert (= a true))
(assert (= a false))
(check-sat)

