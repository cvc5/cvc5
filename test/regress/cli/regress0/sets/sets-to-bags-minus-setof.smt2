; COMMAND-LINE: --sets-to-bags=setof
; EXPECT: unsat
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(assert (set.member x A))
(assert (set.member x B))
(assert (set.member x (set.minus A B)))
(check-sat)
