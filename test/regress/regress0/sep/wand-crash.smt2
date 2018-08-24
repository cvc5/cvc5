; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(assert (wand (_ emp Int Int) (_ emp Int Int)))
(check-sat)
