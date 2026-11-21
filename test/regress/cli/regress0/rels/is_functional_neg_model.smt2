; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple Int Int)))
(declare-fun S () (Set (Tuple Int Int)))
(assert (not (rel.is-functional R)))
(assert (set.subset R S))
(assert (rel.is-functional (rel.transpose S)))
(check-sat)
