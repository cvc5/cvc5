; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; COMMAND-LINE: --sets-exp --rels-functional-mode=iden
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple Int Int)))
(declare-fun S () (Set (Tuple Int Int)))
(assert (not (rel.is_functional R)))
(assert (set.subset R S))
(assert (rel.is_functional (rel.transpose S)))
(check-sat)
