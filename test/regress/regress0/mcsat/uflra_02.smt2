(set-logic QF_UFLRA)

(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)

(assert (not (= (f (+ 1 (f x) (f y))) (f (+ 1 (f x) (f z))))))

(check-sat)
(exit)
