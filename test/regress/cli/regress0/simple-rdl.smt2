(set-logic QF_RDL)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (=> (< (- x y) 0) (< x y))))
(check-sat)

