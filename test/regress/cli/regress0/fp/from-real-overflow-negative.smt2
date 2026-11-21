; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
; Satisfiable negative overflow: the model has to pick an x at or below the
; negative overflow threshold of Float32 under RNE.
(set-logic ALL)
(declare-const x Real)
(assert (fp.isInfinite ((_ to_fp 8 24) RNE x)))
(assert (fp.isNegative ((_ to_fp 8 24) RNE x)))
(check-sat)
