(set-logic QF_LRA)
(set-info :smt-lib-version 2.0)
(set-info :status sat)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (< 2 (+ x y)))
(assert (<= (+ x y) 1))

(check-sat)
(exit)
