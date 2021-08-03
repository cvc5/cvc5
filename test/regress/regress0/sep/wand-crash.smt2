; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (wand (_ emp Int Int) (_ emp Int Int)))
(check-sat)
