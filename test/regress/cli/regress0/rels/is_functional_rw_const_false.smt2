; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(assert (rel.is_functional (set.insert (tuple 1 2) (set.singleton (tuple 1 3)))))
(check-sat)
