(set-logic QF_UFLRA)

(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun f (Real) Real)

(assert (or (= x 1) (= x 2)))

(assert (not (= (f 1) (f x))))
(assert (not (= (f 2) (f x))))

(check-sat)
(exit)
