; EXPECT: unsat
(set-logic ALL)
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(assert (= (bvmul b #b1110 c) (bvmul b c)))
(assert (not (= (bvmul b c) #b0000)))
(check-sat)
