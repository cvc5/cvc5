; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; SymFPU's roundToIntegral() did not overflow to infinity for formats where
; the largest finite values are not integral.
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 3 5))
(assert (fp.gt a (fp #b0 #b110 #b1110)))
(assert (not (fp.isInfinite a)))
(push 1)
(assert (fp.isInfinite (fp.roundToIntegral RNE a)))
(set-info :status sat)
(check-sat)
(pop 1)
(push 1)
(assert (not (fp.isInfinite (fp.roundToIntegral RNE a))))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (fp.isInfinite (fp.roundToIntegral RTZ a)))
(set-info :status unsat)
(check-sat)
