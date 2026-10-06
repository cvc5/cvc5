; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple Int Int)))
(declare-fun S () (Set (Tuple Int Int)))
(declare-fun x () Int)
(assert (rel.is_functional R))
(assert (= R S))
(assert (set.member (tuple x 1) S))
(assert (set.member (tuple x 2) S))
(check-sat)
