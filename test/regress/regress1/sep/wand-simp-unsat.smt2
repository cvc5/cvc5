; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_ALL)
(declare-fun x () Int)
(declare-heap (Int Int))
(assert (wand (pto x 1) (pto x 3)))
(assert sep.emp)
(check-sat)
