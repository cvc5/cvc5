; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const c (_ BitVec 1))
(declare-const x (_ BitVec 4))
(assert (not (=
	(bvite c #b0 #b1)
	(bvnot c)
	)))
(check-sat)
(exit)
