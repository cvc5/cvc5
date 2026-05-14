; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(declare-const t (_ BitVec 8))
(assert (= ((_ int_to_bv 8) 0) ((_ int_to_bv 8) (to_int (+ 0.49 (* (to_real (ubv_to_int t)) (/ (to_real (ubv_to_int ((_ int_to_bv 8) (to_int (ite (is_int (/ (to_real (ubv_to_int t)) 3.5)) (to_real (ubv_to_int t)) 0.0))))) 255.0)) (* (to_real (ubv_to_int (_ bv255 8))) (- 1.0 (/ (to_real (ubv_to_int ((_ int_to_bv 8) (to_int (ite (is_int (/ (to_real (ubv_to_int t)) 3.5)) (to_real (ubv_to_int t)) 0.0))))) 255.0))))))))
(check-sat)
