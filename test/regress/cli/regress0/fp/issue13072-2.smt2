; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp --check-models --simplification=none
; EXPECT: sat
; EXPECT: ((x (fp #b0 #b00 #b01)))
; SymFPU packed the smallest subnormal of (_ FloatingPoint 2 3) as +zero.
(set-logic QF_FP)
(set-option :produce-models true)
(declare-const y Float64)
(declare-const x (_ FloatingPoint 2 3))
; y = 0.3
(assert (= y (fp #b0 #b01111111101 #b0011001100110011001100110011001100110011001100110011)))
(assert (= x ((_ to_fp 2 3) RTN y)))
(check-sat)
(get-value (x))
