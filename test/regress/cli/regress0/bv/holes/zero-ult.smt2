; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	(bvult #b00000 x)
	(not (= x #b00000))
	)))
(check-sat)
(exit)
