; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(assert (wand (emp 0) (emp 0)))
(check-sat)
