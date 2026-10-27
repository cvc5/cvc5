; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(assert (not (rel.is-functional (set.insert (tuple 1 2) (tuple 2 2) (set.singleton (tuple 3 2))))))
(check-sat)
