; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(declare-fun S () (Set (Tuple U U)))
(assert (rel.is_functional R))
(assert (rel.is_functional S))
(assert (not (rel.is_functional (rel.join R S))))
(check-sat)
