; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(declare-const z (_ BitVec 5))
(declare-const w (_ BitVec 5))
(assert (not (=
	(bvmul x (bvmul y z) w)
	(bvmul x y z w))))
(check-sat)
(exit)
