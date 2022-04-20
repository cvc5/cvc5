(set-logic BV)
(set-info :status unsat)
(declare-fun k_42 () (_ BitVec 32))
(declare-fun k_332 () (_ BitVec 32))
(declare-fun k_28 () (_ BitVec 32))

(assert (and 
(bvult k_332 k_42)

(forall ((x (_ BitVec 32)) (y (_ BitVec 32))) (or 
  (and (not (bvult y (_ bv65539 32))) (not (= (_ bv1 32) x))) 
  (not (bvult k_332 (bvmul x k_42)))) )
)
)

(check-sat)
