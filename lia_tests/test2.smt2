(set-logic QF_LIA)

(declare-const a Int)
(declare-const b Int)
(assert (= (+ a 1) (+ b 2)))
(assert (< a 5))
(check-sat)
