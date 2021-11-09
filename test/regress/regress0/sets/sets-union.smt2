; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(define-sort SetInt () (Set Int))
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun x () Int)
(assert (not (set.member x a)))
(assert (set.member x (set.union a b)))
(check-sat)
;(get-model)
(assert (not (set.member x b)))
(check-sat)
(exit)
