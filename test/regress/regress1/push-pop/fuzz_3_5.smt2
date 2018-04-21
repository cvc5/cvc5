; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (< (+ (* 23 x1 ) (* (- 27) x1 ) (* 22 x0 ) ) (- 22)) )
(assert (>= (+ (* (- 4) x0 ) (* (- 9) x1 ) (* (- 40) x0 ) (* 40 x2 ) ) (- 27)) )
(assert (or (not (>= (+ (* (- 34) x0 ) (* (- 36) x1 ) ) (- 26))) (not (>= (+ (* 6 x2 ) (* (- 6) x1 ) ) (- 43))) ))
(assert (or (>= (+ (* 20 x2 ) (* 12 x0 ) (* (- 50) x1 ) ) (- 46)) (not (> (+ (* 11 x1 ) (* (- 30) x0 ) ) (- 21))) ))
(check-sat)
(push 1)
(assert (or (not (>= (+ (* (- 17) x2 ) (* 25 x1 ) (* 43 x0 ) (* (- 9) x0 ) ) (- 19))) (> (+ (* 4 x1 ) (* (- 22) x1 ) ) 8) (> (+ (* 19 x1 ) (* (- 1) x1 ) (* (- 22) x1 ) (* (- 47) x2 ) ) 46) ))
(assert (or (> (+ (* (- 12) x1 ) (* 25 x1 ) ) (- 18)) (not (= (+ (* (- 47) x0 ) (* (- 13) x2 ) (* (- 13) x1 ) (* (- 10) x0 ) ) (- 27))) ))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (not (>= (+ (* 9 x2 ) (* (- 18) x1 ) (* (- 7) x0 ) (* (- 2) x2 ) ) (- 40))) (< (+ (* 2 x1 ) (* (- 4) x1 ) (* (- 48) x2 ) ) 32) ))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (<= (+ (* (- 10) x2 ) (* (- 20) x1 ) (* 9 x2 ) ) 23)) )
(check-sat)
(pop 1)
(check-sat)
(push 1)
