; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp --incremental
; EXPECT: sat
; EXPECT: unsat
; SymFPU's roundToIntegral() called matchWidth() on the rounding point for
; formats where the significand is as wide as the unpacked exponent.
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 3 4))
(assert (fp.lt (fp #b0 #b100 #b000) a))
(assert (fp.lt a (fp #b0 #b100 #b100)))
(assert (fp.eq (fp.roundToIntegral RNE a) (fp #b0 #b100 #b000)))
(push 1)
(set-info :status sat)
(check-sat)
(pop 1)
(assert (fp.gt a (fp #b0 #b100 #b010)))
(set-info :status unsat)
(check-sat)
