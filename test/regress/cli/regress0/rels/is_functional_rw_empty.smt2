; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(assert (not (rel.is-functional (as set.empty (Set (Tuple Int Int))))))
(check-sat)
