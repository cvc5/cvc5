; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-fun x () Int)
(assert (wand (_ emp Int Int) (pto x 3)))
(check-sat)

