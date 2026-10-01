; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic BVSNIRA)
(declare-const x Int)
(declare-const q Int)
(declare-const h Int)
(assert (= h (* q (- q 1))))
(declare-const d Int)
(assert (and (> d 1) (< d h)))
(assert (= 1
           (ite (bvsmulo ((_ int_to_bv 8) 3) ((_ int_to_bv 8) d))
                (ite (> (str.indexof
                         (str.++ (str.from_int 0) (str.from_int x)) "1" 0)
                        -1)
                     1
                     0)
                (to_int (ite (is_int (/ 1.0 (+ 0.0001 (to_real h))))
                             1.0
                             0.0)))))
(assert (or (= x 0) (= q 4)))
(check-sat)
