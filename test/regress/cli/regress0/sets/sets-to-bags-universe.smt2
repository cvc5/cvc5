; COMMAND-LINE: --sets-to-bags=setof --sets-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (set.member x A))
(assert (set.member x (set.complement A)))
(assert (set.member y B))
(assert (not (set.member y (as set.universe (Set Int)))))
(check-sat)
