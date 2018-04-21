; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
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
(assert (or (not (> (+ (* (- 25) x0 ) (* 16 x2 ) ) 21)) (>= (+ (* 18 x1 ) (* (- 35) x0 ) (* 18 x0 ) (* 24 x0 ) ) (- 50)) ))
(assert (> (+ (* (- 40) x0 ) (* 29 x2 ) ) 9) )
(check-sat)
(push 1)
(assert (or (not (> (+ (* 32 x1 ) (* (- 23) x0 ) (* 46 x2 ) ) 11)) (not (< (+ (* (- 12) x0 ) (* (- 40) x0 ) (* 43 x2 ) (* (- 13) x1 ) ) 49)) ))
(assert (not (>= (+ (* (- 47) x0 ) (* 24 x1 ) ) 32)) )
(check-sat)
(pop 1)
(assert (or (= (+ (* 8 x0 ) (* 31 x1 ) (* 38 x1 ) ) (- 31)) (<= (+ (* (- 16) x1 ) (* (- 22) x2 ) (* 27 x2 ) (* (- 23) x0 ) ) (- 12)) ))
(assert (or (not (>= (+ (* 43 x1 ) (* (- 29) x1 ) (* 32 x0 ) (* (- 29) x1 ) ) (- 10))) (>= (+ (* 24 x0 ) (* (- 31) x1 ) ) 34) ))
(assert (or (not (>= (+ (* (- 39) x2 ) (* (- 48) x2 ) (* (- 46) x0 ) (* 2 x1 ) ) 19)) (not (<= (+ (* (- 44) x0 ) (* (- 36) x2 ) ) (- 23))) ))
(check-sat)
(push 1)
(assert (not (<= (+ (* 37 x1 ) (* 19 x2 ) (* 24 x1 ) (* (- 15) x0 ) ) (- 12))) )
(assert (or (>= (+ (* (- 24) x0 ) (* (- 29) x0 ) (* 40 x2 ) ) (- 39)) (not (<= (+ (* (- 41) x0 ) (* 40 x2 ) (* 41 x1 ) (* (- 3) x0 ) ) 28)) ))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (not (> (+ (* 38 x0 ) (* (- 47) x0 ) (* 19 x0 ) (* 40 x2 ) ) (- 39))) (not (< (+ (* 30 x2 ) (* 39 x1 ) ) (- 28))) ))
(assert (or (>= (+ (* (- 12) x0 ) (* (- 26) x1 ) (* (- 13) x1 ) ) 28) (> (+ (* (- 10) x0 ) (* (- 32) x1 ) ) 12) ))
(check-sat)
(push 1)
(assert (< (+ (* (- 33) x2 ) (* (- 13) x0 ) ) 42) )
(assert (or (not (= (+ (* 17 x2 ) (* 4 x2 ) ) 7)) (<= (+ (* 19 x1 ) (* 22 x1 ) (* 19 x1 ) ) 26) (not (<= (+ (* 9 x2 ) (* 0 x0 ) (* 24 x2 ) ) (- 10))) ))
(assert (< (+ (* 45 x1 ) (* (- 38) x0 ) (* 19 x2 ) (* 17 x1 ) ) (- 14)) )
(check-sat)
(pop 1)
(assert (not (< (+ (* 10 x0 ) (* (- 31) x2 ) (* (- 21) x0 ) ) (- 29))) )
(check-sat)
(pop 1)
(check-sat)
(push 1)
