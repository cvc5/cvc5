; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-fun v () Real)
(assert (forall ((V Real)) (> 0.0 (/ 0.0 v))))
(assert (= 0.0 (* (sin v) (sin 1.0))))
(check-sat)
