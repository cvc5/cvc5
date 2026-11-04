; EXPECT: sat
(set-logic QF_BV)
(declare-const a (_ BitVec 2))
(declare-const x (_ BitVec 1))
(assert (and (= a #b01) (= x #b0) (bvslt (bvmul ((_ zero_extend 2) a) ((_ sign_extend 3) (bvadd x #b1))) (bvmul ((_ zero_extend 2) a) ((_ sign_extend 3) x)))))
(check-sat)
