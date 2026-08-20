; REQUIRES: unrestricted-mode
; COMMAND-LINE: --debug-check-models
; EXPECT: sat
; With --debug-check-models, TheoryEngine::checkTheoryAssertionsWithModel
; evaluates each theory's asserted facts against the model. Separation logic
; facts are labeled spatial atoms that the generic evaluator cannot check;
; they are now evaluated against the concrete heap model, so this no longer
; emits "THEORY_SEP has an asserted fact that the model may not satisfy"
; warnings (i.e. the expected error output is empty).
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 2) (pto 3 4)))
(check-sat)
