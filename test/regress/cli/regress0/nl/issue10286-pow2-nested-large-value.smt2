; REQUIRES: unrestricted-mode
; COMMAND-LINE: --no-nl-ext-rewrite --nl-ext=none
; EXPECT: unknown
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 1000))
(assert (> y (int.pow2 (int.pow2 x))))
(check-sat)
