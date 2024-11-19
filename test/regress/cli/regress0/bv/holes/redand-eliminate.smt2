; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 6))
(assert (not (=
	(bvredand x)
	(bvcomp x #b111111)
	)))
(check-sat)
(exit)
