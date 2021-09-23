(set-logic QF_LIA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(assert (let
	   ((a 2))
	   (= a (let ((a 7)) a))))
(check-sat)
(exit)

