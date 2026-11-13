; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun A () (Set (Tuple Int)))
(assert (not (rel.is-functional (rel.iden A))))
(check-sat)
