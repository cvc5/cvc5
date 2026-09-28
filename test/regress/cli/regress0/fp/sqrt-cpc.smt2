; REQUIRES: unrestricted-mode
; EXPECT: unsat
; Exercise the rounding-mode argument of fp.sqrt in CPC proofs.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (distinct (fp.sqrt RNE x) (fp.sqrt RNE x)))
(check-sat)
