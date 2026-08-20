; COMMAND-LINE: --check-models
; EXPECT: sat
; Tests that check-models evaluates the empty heap constraint against the heap
; model.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert sep.emp)
(check-sat)
