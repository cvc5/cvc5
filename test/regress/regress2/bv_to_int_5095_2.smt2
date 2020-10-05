; EXPECT: sat
(set-logic BV)
(set-option :solve-bv-as-int sum)
(declare-const bv_42-0 (_ BitVec 42))
(assert (exists ((q26 (_ BitVec 6)) (q27 (_ BitVec 28)) (q28 (_ BitVec 42))) (not (bvugt (bvudiv bv_42-0 bv_42-0) q28))))
(check-sat)