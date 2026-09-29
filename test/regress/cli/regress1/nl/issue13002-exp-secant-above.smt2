; REQUIRES: unrestricted-mode
; COMMAND-LINE: -q
; EXPECT: sat
;
; Variant of issue13002-exp-secant-bound.smt2 that only involves exp. Note
; that v = 1.9 is a solution, since exp(1.9) is about 6.69.
(set-logic ALL)
(declare-fun v () Real)
(assert (< v 2.0))
(assert (> v 1.0))
(assert (> (exp v) 6.0))
(check-sat)
