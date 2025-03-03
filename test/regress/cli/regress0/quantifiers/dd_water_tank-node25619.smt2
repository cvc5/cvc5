; EXPECT: unsat
(set-logic ALL)
(assert (forall ((t (_ BitVec 32))) (bvsle (_ bv0 32) (bvmul t (bvneg (_ bv2 32))))))
(check-sat)
