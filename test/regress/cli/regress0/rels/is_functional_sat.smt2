; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple Int Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (rel.is-functional R))
(assert (set.member (tuple x y) R))
(assert (set.member (tuple z y) R))
(assert (set.member (tuple z 7) R))
(assert (distinct x z))
(check-sat)
