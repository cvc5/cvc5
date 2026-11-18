; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 5))
(declare-const r (_ FloatingPoint 3 5))
(assert (fp.gt x (fp #b0 #b110 #b1110)))
(assert (not (fp.isInfinite x)))
(assert (= r (fp.roundToIntegral RTP x)))
(assert (not (fp.isInfinite r)))
(assert (fp.gt r (fp #b0 #b110 #b1111)))
(check-sat)
