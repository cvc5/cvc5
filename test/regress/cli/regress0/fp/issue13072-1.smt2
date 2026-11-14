; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp --check-models
; EXPECT: sat
; EXPECT: ((x (fp #b0 #b00 #b01)))
; SymFPU packed the smallest subnormal of (_ FloatingPoint 2 3) as +zero.
(set-logic QF_FP)
(set-option :produce-models true)
(declare-const x (_ FloatingPoint 2 3))
(assert (fp.isSubnormal x))
(assert (fp.isPositive x))
(assert (fp.lt x (fp #b0 #b00 #b10)))
(check-sat)
(get-value (x))
