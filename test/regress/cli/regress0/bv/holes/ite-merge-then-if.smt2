; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const c0 (_ BitVec 1))
(declare-const c1 (_ BitVec 1))
(declare-const t0 (_ BitVec 4))
(declare-const t1 (_ BitVec 4))
(declare-const e0 (_ BitVec 4))
(declare-const e1 (_ BitVec 4))
(assert (not (=
	(bvite c0 (bvite c1 t1 e1) t1)
	(bvite (bvand c0 (bvnot c1)) e1 t1)
	)))
(check-sat)
(exit)
