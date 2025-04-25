; EXPECT: unsat
(set-logic ALL)
(declare-fun I () (_ BitVec 8))
(assert (= (_ bv1 1) ((_ extract 0 0) (ite (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv1 32) (bvand (_ bv33553921 32) ((_ sign_extend 24) I)))))) (_ bv1 32) (_ bv0 32)))))
(check-sat)
