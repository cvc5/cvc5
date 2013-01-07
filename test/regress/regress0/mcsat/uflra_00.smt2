(set-logic QF_UFLRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun f (Real) Real)

(assert (= x y))
(assert (not (= (f (+ x y)) (f y))))

(check-sat)
(exit)
