; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
; SymFPU's unpacked exponent was too narrow to represent the significand size
; for exponent size 2 and a significand size that is a power of two.
(set-logic QF_FP)
(declare-const rm RoundingMode)
(declare-const x (_ FloatingPoint 2 4))
(assert (not (= rm RNA)))
(assert (not (= rm RTP)))
(assert (not (= rm RTN)))
(assert (not (= rm RTZ)))
(assert (fp.eq x (fp #b0 #b01 #b000)))
(assert (not (fp.eq (fp.roundToIntegral rm x) x)))
(set-info :status unsat)
(check-sat)
