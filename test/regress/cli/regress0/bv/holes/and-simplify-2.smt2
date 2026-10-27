; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))
(declare-const w (_ BitVec 4))
(assert (not (=
	(bvand x y z (bvnot y) w)
	#b0000
	)))
(check-sat)
(exit)
