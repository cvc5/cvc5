; COMMAND-LINE: --check-model
; EXPECT: (error "Cannot run check-model on a model with approximate values.")
; EXIT: 1
(set-logic QF_UFNRAT)
(set-option :produce-models true)
(declare-fun b (Real) Real)
(declare-fun v () Real)
(assert (distinct 0 (* v v)))
(assert (= 0.0 (b (exp 1.0))))
(check-sat)
