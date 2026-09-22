; EXPECT: unsat
(set-logic ALL)
(assert (forall ((x (_ BitVec 32))) (forall ((y (_ BitVec 32))) (not (= (_ bv0 32) (bvadd x (bvmul y (_ bv65 32))))))))
(check-sat)
