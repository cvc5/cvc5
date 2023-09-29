; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(assert (not (=
	(bvult ((_ sign_extend 3) x) #b000010)
	(bvult x #b010)
	)))
(check-sat)
(exit)
