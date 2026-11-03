; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
; SymFPU's unpacked exponent was too narrow for significand size <= 3.
(set-logic QF_BVFP)
(declare-const b (_ BitVec 4))
(assert (bvuge b #b0100))
(assert (bvule b #b0100))
(assert (distinct ((_ to_fp_unsigned 5 3) RNA b) (fp #b0 #b10001 #b00)))
(set-info :status unsat)
(check-sat)
