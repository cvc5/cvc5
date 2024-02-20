; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const c (_ BitVec 1))
(declare-const t0 (_ BitVec 4))
(declare-const t1 (_ BitVec 4))
(declare-const e (_ BitVec 4))
(assert (not (=
	(bvite c t0 (bvite c t1 e))
	(bvite c t0 e)
	)))
(check-sat)
(exit)
