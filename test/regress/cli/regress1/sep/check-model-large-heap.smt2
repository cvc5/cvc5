; COMMAND-LINE: --check-models
; EXPECT: sat
; A heap with more cells than the fixed cell-count cutoff the partition
; search used to have, where check-models either gave up or, worse,
; reported this satisfied assertion as violated. The search is bounded by
; a budget instead now, and a conjunct whose cell count is fixed by its
; syntax only ever generates fragments of that one size, so deciding this
; costs O(n^2) candidate fragments rather than O(n^n).
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 1) (pto 2 2) (pto 3 3) (pto 4 4) (pto 5 5) (pto 6 6) (pto 7 7) (pto 8 8) (pto 9 9) (pto 10 10) (pto 11 11) (pto 12 12) (pto 13 13) (pto 14 14) (pto 15 15) (pto 16 16) (pto 17 17)))
(assert (not sep.emp))
(check-sat)
