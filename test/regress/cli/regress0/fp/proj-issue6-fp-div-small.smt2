; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: sat
(set-logic QF_FP)
(declare-fun r () (_ FloatingPoint 3 5))
(assert (= r (fp.div RNE (fp #b0 #b000 #b0000) (fp #b0 #b000 #b0000))))
(check-sat)
