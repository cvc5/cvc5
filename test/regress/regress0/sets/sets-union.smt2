; COMMAND-LINE: --incremental --no-check-model
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(define-sort SetInt () (Set Int))
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun x () Int)
(assert (not (in x a)))
(assert (in x (union a b)))
(check-sat)
;(get-model)
(assert (not (in x b)))
(check-sat)
(exit)
