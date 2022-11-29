; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun v () Real)
(assert (xor (= 0.0 (/ v 0.0)) (distinct 1.0 (/ 0 0))))
(assert (forall ((V Real)) (distinct 0.0 (sin 1.0))))
(check-sat)
