; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic QF_FP)
(set-option :fp-exp true)
(declare-fun r () (_ FloatingPoint 4 4))
(assert (= r (fp.mul RNE (fp #b0 #b0000 #b000) (fp #b0 #b0000 #b000))))
(check-sat)
