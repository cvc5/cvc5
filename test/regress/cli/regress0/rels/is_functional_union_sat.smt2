; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(declare-fun S () (Set (Tuple U U)))
(assert (rel.is-functional R))
(assert (rel.is-functional S))
(assert (not (rel.is-functional (set.union R S))))
(check-sat)
