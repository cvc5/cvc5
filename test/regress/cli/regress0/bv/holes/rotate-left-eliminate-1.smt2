; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	((_ rotate_left 5) x)
	(concat ((_ extract 4 0) x) ((_ extract 9 5) x))
	)))
(check-sat)
(exit)
