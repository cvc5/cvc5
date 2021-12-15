; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat

; x not in A U B => x not in A
(set-logic ALL)
(define-sort SetInt () (Bag Int))
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun x () Int)
(assert (not (>= (bag.count x (bag.union_disjoint A B)) 1)))
(push 1)
(assert (>= (bag.count x B) 1))
(check-sat)
(pop 1)
(check-sat)
