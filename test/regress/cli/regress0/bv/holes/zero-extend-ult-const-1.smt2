; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(assert (not (=
	(bvult ((_ zero_extend 3) x) #b000110)
	(bvult x #b110)
	)))
(check-sat)
(exit)
