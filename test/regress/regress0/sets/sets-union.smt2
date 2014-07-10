; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(define-sort SetInt () (Set Int))
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun x () Int)
(assert (not (member x a)))
(assert (member x (union a b)))
(check-sat)
;(get-model)
(assert (not (member x b)))
(check-sat)
(exit)
