; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(assert (not (= (_ bv1 1) ((_ extract 0 0) (ite (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 31 24) ((_ zero_extend 24) ((_ extract 31 24) (bvand (_ bv510 32) (_ bv1 32) (ite x (_ bv1 32) (_ bv0 32)))))))) (_ bv1 32) (_ bv0 32))))))
(check-sat)
