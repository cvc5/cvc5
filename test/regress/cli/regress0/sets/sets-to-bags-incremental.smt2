; COMMAND-LINE: --sets-to-bags=setof --incremental --sets-exp
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun x () Int)
(define-fun S () (Set Int) (set.union A (set.singleton 5)))
(define-fun f ((X (Set Int))) Bool (set.member x X))
(assert (f A))
(push 1)
(assert (set.member x (set.minus (set.singleton 1) A)))
(check-sat)
(pop 1)
(push 1)
(assert (not (set.member x S)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (set.member x (set.complement S)))
(check-sat)
(pop 1)
(check-sat)
