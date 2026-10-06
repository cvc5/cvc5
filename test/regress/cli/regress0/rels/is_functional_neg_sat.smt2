; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(assert (not (rel.is_functional R)))
(check-sat)
