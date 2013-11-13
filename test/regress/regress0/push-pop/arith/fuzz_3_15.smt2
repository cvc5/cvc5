; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (not (<= (+ (* (- 3) x0 ) (* 38 x0 ) (* 34 x1 ) ) (- 5))) )
(assert (or (not (> (+ (* (- 27) x0 ) (* 26 x1 ) ) (- 50))) (not (>= (+ (* 32 x0 ) (* 10 x0 ) (* (- 43) x1 ) (* (- 39) x0 ) ) (- 36))) ))
(check-sat)
(push 1)
(assert (> (+ (* (- 23) x2 ) (* 49 x2 ) ) 14) )
(assert (not (= (+ (* 20 x1 ) (* (- 38) x2 ) ) 33)) )
(assert (not (<= (+ (* 30 x0 ) (* (- 13) x1 ) (* 21 x1 ) ) 20)) )
(assert (or (<= (+ (* 48 x0 ) (* (- 42) x0 ) (* 34 x1 ) (* 47 x1 ) ) 12) (not (>= (+ (* 0 x1 ) (* (- 1) x1 ) (* (- 19) x1 ) ) 40)) (not (>= (+ (* (- 40) x2 ) (* 3 x2 ) (* 4 x0 ) (* 19 x2 ) ) 34)) ))
(assert (or (= (+ (* (- 7) x1 ) (* 15 x0 ) (* (- 12) x0 ) ) 6) (not (<= (+ (* (- 41) x2 ) (* 10 x0 ) (* 12 x2 ) ) 49)) ))
(assert (or (<= (+ (* 12 x2 ) (* (- 50) x1 ) ) (- 25)) (= (+ (* (- 29) x2 ) (* (- 11) x2 ) (* (- 8) x2 ) (* (- 3) x2 ) ) (- 39)) ))
(assert (or (= (+ (* 33 x2 ) (* 44 x0 ) (* (- 4) x1 ) ) 5) (not (< (+ (* 27 x2 ) (* (- 45) x0 ) (* 43 x2 ) (* 40 x0 ) ) 17)) (not (<= (+ (* (- 40) x2 ) (* 3 x0 ) (* 16 x2 ) (* (- 37) x1 ) ) 29)) ))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (= (+ (* (- 21) x0 ) (* 5 x2 ) ) (- 27)) (not (<= (+ (* (- 20) x0 ) (* 19 x0 ) (* (- 50) x1 ) (* (- 24) x0 ) ) (- 32))) ))
(check-sat)
(pop 1)
(assert (not (<= (+ (* 9 x2 ) (* 0 x0 ) (* (- 40) x0 ) (* 49 x2 ) ) (- 11))) )
(assert (or (not (< (+ (* (- 2) x0 ) (* 2 x2 ) ) 19)) (= (+ (* (- 28) x1 ) (* (- 1) x2 ) (* (- 4) x1 ) ) 38) ))
(check-sat)
(push 1)
