; COMMAND-LINE: --incremental --produce-models --block-models=literals
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(assert (or (= x 4) (= x 5) (= x 6) (= x 7)))
(check-sat)
(block-model-values (x))
(check-sat)
(block-model)
(check-sat)
(block-model-values ((+ x 1)))
(check-sat)
(block-model)
(check-sat)
