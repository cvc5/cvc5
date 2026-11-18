; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
; SymFPU's convertFloatToFloat() took the fast path for strict promotions
; although the exponent range of the target format is smaller.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 4 4))
(assert (fp.gt x (fp #b0 #b1101 #b000)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isInfinite ((_ to_fp 2 9) RNE x))))
(set-info :status unsat)
(check-sat)
