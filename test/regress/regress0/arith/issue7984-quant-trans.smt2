; COMMAND-LINE: --check-models
; EXPECT: (error "Cannot run check-model on a model with approximate values.")
; EXIT: 1
(set-logic QF_NRAT)
(set-option :re-elim-agg true)
(declare-fun r6 () Real)
(assert (= 0.0 (cos r6)))
(check-sat)