; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Set (Set Int)))
(declare-fun x () (Set Int))
(assert (set.member x A))
(assert (set.member 3 (set.choose A)))
(assert (not (set.member 3 x)))
(check-sat)
