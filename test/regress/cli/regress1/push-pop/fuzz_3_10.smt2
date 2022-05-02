; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (or (not (<= (+ (* 30 x2 ) (* 34 x2 ) (* 16 x2 ) ) 30)) (not (>= (+ (* (- 7) x1 ) (* 5 x1 ) ) (- 36))) ))
(assert (= (+ (* (- 33) x2 ) (* (- 46) x0 ) (* (- 32) x1 ) ) (- 30)) )
(assert (or (>= (+ (* (- 35) x1 ) (* (- 29) x1 ) (* 30 x1 ) (* 20 x1 ) ) 27) (> (+ (* 30 x1 ) (* 33 x0 ) ) 16) (= (+ (* (- 28) x2 ) (* 7 x1 ) (* 8 x0 ) ) 37) ))
(assert (or (< (+ (* 6 x2 ) (* (- 12) x1 ) ) (- 14)) (not (<= (+ (* (- 23) x1 ) (* 44 x1 ) ) 9)) (not (<= (+ (* (- 18) x2 ) (* 16 x0 ) (* 47 x0 ) ) 25)) ))
(assert (or (< (+ (* (- 8) x1 ) (* 12 x2 ) (* 23 x1 ) ) (- 50)) (not (> (+ (* 37 x1 ) (* (- 30) x2 ) (* 1 x0 ) (* 13 x1 ) ) (- 22))) ))
(check-sat)
(push 1)
(assert (or (not (= (+ (* (- 3) x0 ) (* (- 49) x1 ) ) 25)) (<= (+ (* 47 x2 ) (* 9 x0 ) ) (- 5)) ))
(assert (or (not (< (+ (* 34 x0 ) (* 28 x0 ) (* 36 x0 ) (* 1 x0 ) ) (- 9))) (>= (+ (* (- 4) x2 ) (* 15 x1 ) (* (- 35) x0 ) (* (- 2) x1 ) ) (- 20)) ))
(assert (not (<= (+ (* (- 4) x1 ) (* 22 x1 ) (* 22 x2 ) (* (- 33) x0 ) ) 12)) )
(check-sat)
(pop 1)
(assert (<= (+ (* 36 x0 ) (* (- 25) x2 ) (* 48 x2 ) (* (- 14) x1 ) ) (- 9)) )
(check-sat)
