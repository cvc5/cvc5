; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	(bvshl x #b0100000000)
	#b0000000000
	)))
(check-sat)
(exit)
