; COMMAND-LINE: --check-models
; EXPECT: sat
; Tests that check-models evaluates a separating conjunction against the heap
; model by searching for a satisfying partition of the heap.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 2) (pto 3 4)))
(check-sat)
