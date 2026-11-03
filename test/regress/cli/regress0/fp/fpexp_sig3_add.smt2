; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: sat
; SymFPU's unpacked exponent was too narrow for significand size <= 3.
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 2 3))
(declare-const b (_ FloatingPoint 2 3))
(assert (fp.isNormal a))
(assert (fp.isNegative a))
(assert (fp.isPositive b))
(assert (fp.isZero (fp.add RNE a b)))
(set-info :status sat)
(check-sat)
