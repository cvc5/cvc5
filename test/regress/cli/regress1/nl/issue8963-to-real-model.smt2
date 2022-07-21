; COMMAND-LINE: --decision=internal
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun r () Int)
(declare-fun v () Int)
(assert (exists ((V Real)) (distinct (= (to_real v) (* a a)) (>= 0 (* r v (mod v r))))))
(check-sat)
