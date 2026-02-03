; EXPECT: unsat
(set-logic NIRA)
(declare-const p Int)
(declare-const p6 Int)
(declare-const p8 Int)
(assert (and (> (to_real p8) 0.0) (< (to_real p8) (to_real 5))))
(assert (= 2 (mod p (+ 1 (abs p6)))))
(assert (= (* 2 p) (to_int (/ (+ (to_real p) (/ (to_real (- p8)) (+ 0.0 (abs (to_real p6))))) 0.00000001))))
(check-sat)
