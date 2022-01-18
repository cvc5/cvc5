; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat

; x not in A U B => x not in A
(set-logic ALL)
(define-sort SetInt () (Set Int))
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(assert (not (set.member x (set.union A B))))
(push 1)
(assert (set.member x A))
(check-sat)
(pop 1)
(check-sat)
