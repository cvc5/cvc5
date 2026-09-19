; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models --no-check-model-subsolver
; EXPECT: sat
; EXPECT-ERROR: Warning : SolverEngine::checkModel(): cannot check separation logic assertion : (wand (pto 1 1) (pto 2 2))
; DISABLE-TESTER: model
; Without the subsolver fallback, a magic wand assertion cannot be evaluated
; against a single concrete heap model, so check-models leaves it unchecked
; with a warning rather than failing.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (wand (pto 1 1) (pto 2 2)))
(check-sat)
