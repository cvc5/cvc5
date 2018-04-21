; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic LRA)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun x1 () Real)
(assert (forall ((?y1 Real)) (exists ((?y2 Real)) (or (and (>= (+ (+ (* 69 ?y2) (* (- 80) ?y1)) (* 48 x1)) (- 77)) (and (not (= (+ (* (- 1) ?y2) (* (- 48) x1)) 0)) (not (= (+ (* 14 ?y1) (* (- 98) x1)) 83)))) (and (and (<= (+ (+ (* (- 95) ?y2) (* 34 ?y1)) (* (- 54) x1)) 51) (= (+ (+ (* 27 ?y2) (* (- 17) ?y1)) (* 75 x1)) 24)) (not (= (+ (* (- 96) ?y1) (* 90 x1)) (- 39))))))))
(check-sat)
(exit)
