; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 100))
(assert (not (=
	((_ extract 27 23) x)
	((_ extract 7 3) ((_ extract 29 20) x)))))
(check-sat)
(exit)
