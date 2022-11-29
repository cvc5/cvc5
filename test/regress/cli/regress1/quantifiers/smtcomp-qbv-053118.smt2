; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :status sat)
(declare-fun x () (_ BitVec 32))
(assert 
(forall ((u (_ BitVec 32)) (w (_ BitVec 32)) (z (_ BitVec 32)) (m (_ BitVec 32)) (n (_ BitVec 32))) (or 
  (not (= 
    (bvadd (bvmul (_ bv2 32) w) (bvmul (_ bv2 32) n)) 
    (bvadd (bvneg (bvadd (bvmul (_ bv2 32) u) (bvmul (_ bv2 32) z) (bvmul (_ bv2 32) m) x)) (_ bv1 32))
  )) 
))
)
(assert (not 
(and 
  (forall ((m (_ BitVec 32)) (n (_ BitVec 32))) 
    (not (= 
      (bvadd (bvneg (bvadd m x)) (_ bv1 32)) 
      (bvmul (_ bv2 32) n)
    ))
))))
(check-sat)
(exit)
