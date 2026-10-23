; COMMAND-LINE: --sets-to-bags=relaxed
; EXPECT: unknown
; With bag semantics, this is satisfied by A = {|(x, 2)|} and B = {|(x, 1)|}.
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(assert (set.member x A))
(assert (set.member x B))
(assert (set.member x (set.minus A B)))
(check-sat)
