; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(declare-fun x () Int)
(assert (wand (emp x x) (pto x 3)))
(check-sat)

