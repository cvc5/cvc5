; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 2))
(assert (= (_ bv1 1) ((_ extract 0 0) (bvand (_ bv1 32) (bvor (_ bv0 32) (bvand (_ bv131070 32) ((_ sign_extend 24) ((_ zero_extend 1) ((_ zero_extend 5) __)))))))))
(check-sat)
