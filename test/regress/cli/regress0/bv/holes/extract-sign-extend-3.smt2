; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	((_ extract 8 7) ((_ sign_extend 5) x))
	((_ repeat 2) ((_ extract 4 4) x))
	)))
(check-sat)
(exit)
