; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(assert (= (_ bv1 1) (bvand (_ bv1 1) (bvnot ((_ extract 0 0) (ite x (_ bv1 1) (_ bv0 1)))) ((_ extract 0 0) (ite x (_ bv1 1) (_ bv0 1))))))
(check-sat)
