; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const x2 Bool)
(assert (forall ((e (_ BitVec 32))) (and (not (= (ite (not x2) e (_ bv1 32)) (ite (or x2 x) (_ bv1 32) (_ bv0 32)))) (= (_ bv1 1) ((_ extract 0 0) (bvlshr (_ bv1 7) (ite x (_ bv1 7) (_ bv0 7))))))))
(check-sat)
