; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	(bvneg (bvmul x #b10101 y))
	(bvmul x #b01011 y))))
(check-sat)
(exit)
