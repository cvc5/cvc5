; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const c (_ BitVec 1))
(declare-const t (_ BitVec 4))
(declare-const e0 (_ BitVec 4))
(declare-const e1 (_ BitVec 4))
(assert (not (=
	(bvite c (bvite c t e0) e1)
	(bvite c t e1)
	)))
(check-sat)
(exit)
