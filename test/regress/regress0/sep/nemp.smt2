; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_SEP_LIA)
(declare-heap (Int Int))
(assert (not (_ emp Int Int)))
(check-sat)
