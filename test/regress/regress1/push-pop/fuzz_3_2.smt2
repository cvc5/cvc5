; COMMAND-LINE: --incremental
; EXPECT: sat
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
(assert (or (not (>= (+ (* 47 x0 ) (* (- 1) x2 ) (* 13 x2 ) ) (- 9))) (not (< (+ (* 23 x1 ) (* (- 50) x0 ) (* 35 x1 ) (* 12 x2 ) ) 14)) ))
(assert (or (not (<= (+ (* 3 x0 ) (* (- 15) x2 ) (* 34 x0 ) ) (- 39))) (not (> (+ (* (- 35) x0 ) (* 36 x2 ) (* (- 3) x1 ) ) 22)) (not (> (+ (* 46 x2 ) (* 2 x2 ) (* (- 33) x1 ) (* (- 24) x0 ) ) (- 39))) ))
(assert (or (<= (+ (* 27 x1 ) (* 18 x2 ) (* (- 3) x2 ) ) (- 2)) (= (+ (* 27 x0 ) (* (- 26) x2 ) (* 15 x2 ) (* 23 x0 ) ) 11) ))
(assert (or (= (+ (* 23 x1 ) (* (- 1) x1 ) (* (- 3) x2 ) (* 49 x1 ) ) (- 26)) (not (> (+ (* (- 30) x0 ) (* (- 1) x0 ) (* 15 x1 ) ) (- 23))) ))
(check-sat)
(push 1)
(assert (or (not (= (+ (* 24 x1 ) (* 5 x2 ) (* (- 18) x1 ) (* (- 40) x2 ) ) (- 6))) (not (< (+ (* 6 x0 ) (* (- 29) x0 ) (* 16 x2 ) ) (- 42))) ))
(assert (or (= (+ (* (- 33) x0 ) (* 40 x0 ) (* (- 28) x1 ) (* (- 29) x0 ) ) (- 1)) (<= (+ (* (- 17) x1 ) (* 0 x0 ) (* 2 x1 ) ) (- 8)) (not (= (+ (* 39 x2 ) (* 4 x0 ) (* 12 x1 ) (* (- 1) x2 ) ) (- 40))) ))
(check-sat)
(push 1)
(assert (not (<= (+ (* 24 x2 ) (* 9 x2 ) (* 38 x0 ) (* 9 x2 ) ) (- 12))) )
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (> (+ (* (- 33) x1 ) (* 1 x0 ) (* (- 27) x1 ) (* (- 39) x1 ) ) 30)) )
(check-sat)
(pop 1)
(assert (not (>= (+ (* (- 36) x1 ) (* 34 x0 ) (* 39 x0 ) (* 2 x2 ) ) 16)) )
(check-sat)
