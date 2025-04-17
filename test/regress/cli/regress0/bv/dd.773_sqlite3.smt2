; EXPECT: unsat
(set-logic BV)
(declare-const __ (_ BitVec 3))
(declare-fun i () (_ BitVec 32))
(assert (forall ((u (_ BitVec 32))) (and (not (= i (_ bv0 32))) (= (_ bv0 32) (bvor (bvand i u) ((_ zero_extend 16) ((_ zero_extend 8) ((_ zero_extend 4) ((_ zero_extend 1) __)))))))))
(check-sat)
