; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
; Tests that check-models can evaluate a points-to assertion against the
; separation logic heap model (previously this threw a "Cannot run check-model
; on a model with a separation logic heap" error).
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (pto 30 40))
(check-sat)
