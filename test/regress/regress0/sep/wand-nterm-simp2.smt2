; COMMAND-LINE: --no-check-models
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(declare-fun x () Int)
(assert (wand (pto x 1) (emp x)))
(check-sat)
