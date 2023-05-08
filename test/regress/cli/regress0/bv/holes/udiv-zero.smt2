; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	(bvudiv x #b00000)
	#b11111
	)))
(check-sat)
(exit)
