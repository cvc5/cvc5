; EXPECT: unsat
(set-logic ALL)
(assert (forall ((t (_ BitVec 32))) (forall ((c (_ BitVec 32))) (bvslt (bvmul ((_ sign_extend 32) c) ((_ sign_extend 32) (bvadd t (_ bv1 32)))) (bvmul ((_ sign_extend 32) c) ((_ sign_extend 32) t))))))
(check-sat)
