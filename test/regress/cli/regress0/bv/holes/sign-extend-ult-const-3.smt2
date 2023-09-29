; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(assert (not (=
	(bvult #b000010 ((_ sign_extend 3) x))
	(bvult #b010 x)
	)))
(check-sat)
(exit)
