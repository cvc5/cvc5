; REQUIRES: poly
; COMMAND-LINE: --nl-cov
; EXPECT: unknown
(set-logic ALL)
(declare-fun e () Real)
(assert (forall ((x Real)) (distinct (* e e) (+ 1 (* x x (- 1))))))
(check-sat)
