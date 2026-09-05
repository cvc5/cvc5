; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
; DISABLE-TESTER: model
; A separating conjunction containing a magic wand cannot be decided by direct
; evaluation against the concrete heap model, so it must stay opaque and let
; check-models fall back to the subsolver. Evaluating the star's children
; individually against the whole heap instead would make (pto 1 1) false (the
; heap has two cells) and rewrite the star to false, reporting this satisfied
; assertion as violated.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 1) (pto 2 2)))
(assert (sep (pto 1 1) (wand (pto 5 5) true)))
(check-sat)
