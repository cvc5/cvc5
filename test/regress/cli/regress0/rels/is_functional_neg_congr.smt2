; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(declare-fun S () (Set (Tuple U U)))
(assert (not (rel.is_functional R)))
(assert (rel.is_functional S))
(assert (= R S))
(check-sat)
