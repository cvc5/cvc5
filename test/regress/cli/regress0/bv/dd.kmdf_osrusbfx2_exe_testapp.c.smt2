; EXPECT: unsat
(set-logic ALL)
(assert (forall ((c (_ BitVec 32))) (bvslt (bvmul ((_ sign_extend 32) c) ((_ sign_extend 32) (bvadd (_ bv0 32) (_ bv1 32)))) (bvmul ((_ sign_extend 32) c) ((_ sign_extend 32) (_ bv1 32))))))
(check-sat)
