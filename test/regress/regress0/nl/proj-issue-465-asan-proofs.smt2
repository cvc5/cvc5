; COMMAND-LINE: -i -q --produce-proofs
; EXPECT: sat
; EXPECT: sat
(set-logic NRA)
(declare-fun v () Real)
(push)
(assert (and (forall ((V Real)) (and (< 0.0 (/ 0.0 v)) (= (/ 0.0 0.0) (/ (- 1.0) (- v 1.0)))))))
(check-sat)
(pop)
(assert (= 0 (* v v)))
(check-sat)
