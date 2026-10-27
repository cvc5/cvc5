; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 6))
(assert (not (=
	(bvredor x)
	(bvnot (bvcomp x #b000000))
	)))
(check-sat)
(exit)
