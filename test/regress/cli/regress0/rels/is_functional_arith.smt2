; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple Int Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (rel.is-functional R))
(assert (set.member (tuple x 1) R))
(assert (set.member (tuple y 2) R))
(assert (<= 0 x 0))
(assert (<= 0 y 0))
(check-sat)
