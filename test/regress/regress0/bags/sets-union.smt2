; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(define-sort SetInt () (Bag Int))
(declare-fun a () (Bag Int))
(declare-fun b () (Bag Int))
(declare-fun x () Int)
(assert (not (>= (bag.count x a) 1)))
(assert (>= (bag.count x (bag.union_disjoint a b)) 1))
(check-sat)
;(get-model)
(assert (not (>= (bag.count x b) 1)))
(check-sat)
(exit)
