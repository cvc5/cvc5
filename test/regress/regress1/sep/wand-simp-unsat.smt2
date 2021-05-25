; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_ALL_SUPPORTED)
(declare-fun x () Int)
(declare-heap (Int Int))
(assert (wand (pto x 1) (pto x 3)))
(assert (_ emp Int Int))
(check-sat)
