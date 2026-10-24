; COMMAND-LINE: --sets-to-bags=relaxed
; EXPECT: sat
; This is unsat for sets, but sat for bags, e.g. A = {|(x, 2)|} and
; B = {|(x, 1)|}, and --sets-to-bags=relaxed answers for the bags.
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(assert (set.member x A))
(assert (set.member x B))
(assert (set.member x (set.minus A B)))
(check-sat)
