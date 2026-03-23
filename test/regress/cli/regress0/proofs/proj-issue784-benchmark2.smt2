; COMMAND-LINE: --check-proofs --tlimit=100
; EXPECT: sat
(set-logic QF_NIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (+ (+ (- (* 10 x3)) (abs (- (* 11 x2)))) (abs (- 22))) (* (- (* (- (div (* 3 x1) (+ (+ (- (+ (+ (* (- 7) x0) (* 3 x1)) (abs x2)) (+ (+ (+ (* 13 x0) (* (* (* 11 (* 13 x2)) 7) x1)) (* 11 x2)) (* 10 x3))) (- (+ (+ (* 13 x0) (* (- 1) x1)) (* 11 x2)) (+ (* (- 7) x0) (* 3 x1)))) (* (mod 7 10) x3)))) x2) (+ (+ (+ (* 13 (abs (* 13 x0))) (* (- 1) x1)) (* 11 x2)) (* 10 x3))) x3)) (mod (- 1) 16)))
(assert (< (- (div (+ (* (- 7) x0) 3) x2)) (+ (- 22) (* 16 x3))))
(check-sat)
