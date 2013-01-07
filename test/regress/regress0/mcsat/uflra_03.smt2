(set-logic QF_UFLRA)

(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)

(assert (<= (f (f (* 5 x))) (f (f (+ y z))))) 

(check-sat)
(exit)
