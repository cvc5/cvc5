; COMMAND-LINE: --check-models
; EXPECT: sat
; Tests that check-models handles an assertion mixing a spatial atom with a
; non-spatial (heap-independent) constraint, evaluating the latter via the
; usual model evaluation.
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-const x Int)
(assert (and (pto x 5) (> x 0)))
(check-sat)
