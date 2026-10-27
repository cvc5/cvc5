; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun z () Int)
; (div (* 2 z x) (* 4 z)) cannot be factored to (div x 2) since z may be negative
(push)
(assert (= z (- 1)))
(assert (= x 1))
(assert (not (= (div (* 2 z x) (* 4 z)) 1)))
(check-sat)
(pop)
; (mod (* 2 x) 4) cannot be factored to (mod x 2)
(push)
(assert (not (= (mod (* 2 x) 4) (* 2 (mod x 2)))))
(check-sat)
(pop)
; exact division with a non-zero divisor of either sign
(assert (not (= z 0)))
(assert (not (= (div (* z x) (- z)) (- x))))
(check-sat)
