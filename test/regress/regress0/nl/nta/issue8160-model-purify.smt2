; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun b (Int Int) Int)
(declare-fun v () Real)
(declare-fun a () Real)
(assert (forall ((V Real)) (and (= 0 (b 0 0)) (forall ((V Real)) (= 0.0 (sin v))) (exists ((V Real)) (= 1.0 (* a a))))))
(check-sat)
