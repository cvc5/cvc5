; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	(bvor x (bvnot x))
	#b1111111111
	)))
(check-sat)
(exit)
