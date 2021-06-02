; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-fun x () Int)
(assert (wand (pto x 1) (pto x 1)))
(check-sat)
