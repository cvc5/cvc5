; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 4))
(declare-const r (_ FloatingPoint 2 4))
(assert (fp.gt x (fp #b0 #b10 #b110)))
(assert (not (fp.isInfinite x)))
(assert (= r (fp.roundToIntegral RTN x)))
(assert (fp.isZero r))
(check-sat)
