; COMMAND-LINE: --no-check-models
; EXPECT: unsat
(set-logic QF_ALL_SUPPORTED)
(declare-fun x () Int)
(assert (wand (pto x 1) (pto x 3)))
(assert (emp x x))
(check-sat)
