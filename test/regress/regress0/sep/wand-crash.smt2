; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(assert (wand (emp 0 0) (emp 0 0)))
(check-sat)
