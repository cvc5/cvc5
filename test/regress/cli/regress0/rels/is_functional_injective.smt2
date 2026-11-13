; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(assert (rel.is-functional (rel.transpose R)))
(assert (set.member (tuple x y) R))
(assert (set.member (tuple z y) R))
(assert (distinct x z))
(check-sat)
