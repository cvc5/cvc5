; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
; DISABLE-TESTER: model
; A magic wand assertion cannot be evaluated directly against a concrete heap
; model, but check-models can discharge it with a subsolver that pins the heap
; to the model heap. Here the wand holds vacuously (no heap disjoint from the
; model heap satisfies its antecedent), so the model checks out with no error.
;
; Being vacuous, this says nothing about the consequent: the same check passes
; with any consequent at all, including `false'. See
; check-model-wand-nonvacuous.smt2 for a wand that is really quantifying.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (wand (pto 1 1) (pto 2 2)))
(check-sat)
