; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
; DISABLE-TESTER: model
; A magic wand that is genuinely quantifying, unlike check-model-wand-subsolver
; where location 1 is allocated and the wand holds vacuously. Here the heap is
; exactly { 1 -> 1 }, so location 2 is free, { 2 -> 2 } really is disjoint from
; it, and the consequent has to hold of the join. check-models discharges this
; with the subsolver, heap pinned.
;
; That the wand is doing work is checkable: keeping the same heap and replacing
; the consequent with one that cannot hold of { 1 -> 1 } (+) { 2 -> 2 } makes
; the problem unsatisfiable, e.g. `false' or (sep (pto 1 1) (pto 3 3)). The
; vacuous test admits any consequent at all, including `false'.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (pto 1 1))
(assert (wand (pto 2 2) (sep (pto 1 1) (pto 2 2))))
(check-sat)
