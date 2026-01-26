; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const c String)
(assert (= 0 (str.len (str.from_int (ubv_to_int (bvadd ((_ int_to_bv 8) 0) ((_ zero_extend 7) (ite (bvult ((_ int_to_bv 32) 0) ((_ int_to_bv 32) (str.len c))) (_ bv1 1) (_ bv0 1)))))))))
(assert (forall ((i Int)) (exists ((s String)) (or (< i 0) (> i (to_int (to_real (ubv_to_int ((_ extract 7 0) (ite (bvsaddo ((_ int_to_bv 8) (str.len c)) (ite x (_ bv0 8) ((_ int_to_bv 8) 1))) ((_ int_to_bv 16) 1) (_ bv0 16)))))))))))
(check-sat)
