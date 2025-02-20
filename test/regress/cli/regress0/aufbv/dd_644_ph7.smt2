; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 1))
(assert (= (_ bv1 1) ((_ extract 0 0) (bvlshr (concat (bvor (_ bv1 10) ((_ zero_extend 9) x) (ite false (_ bv0 10) (_ bv0 10))) (_ bv0 1)) (_ bv0 11)))))
(check-sat)
