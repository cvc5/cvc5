; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_SEP_LIA)
(assert (not (_ emp Int Int)))
(check-sat)
