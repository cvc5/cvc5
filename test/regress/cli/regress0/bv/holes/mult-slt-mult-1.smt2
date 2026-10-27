; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const t (_ BitVec 5))
(declare-const a (_ BitVec 3))
(assert (not (=
	(bvslt
		(bvmul ((_ sign_extend 5) (bvadd x t)) ((_ sign_extend 7) a))
		(bvmul ((_ sign_extend 5) x) ((_ sign_extend 7) a))
	)
	(and
		(not (= t #b00000))
		(not (= a #b000))
		(= (bvslt (bvadd x t) x) (bvsgt a #b000))
	))))
(check-sat)
(exit)
