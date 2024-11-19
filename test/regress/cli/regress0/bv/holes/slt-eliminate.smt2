; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	(bvslt x y)
	(bvult
		(bvadd x #b10000)
		(bvadd y #b10000)
	)
	)))
(check-sat)
(exit)
