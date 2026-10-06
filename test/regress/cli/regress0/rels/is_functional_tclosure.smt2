; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --rels-functional-mode=pairs
; EXPECT: unsat
(set-logic ALL)
(declare-sort U 0)
(declare-fun R () (Set (Tuple U U)))
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (rel.is_functional R))
(assert (set.member (tuple a b) R))
(assert (set.member (tuple a c) (rel.tclosure R)))
(assert (not (set.member (tuple b c) (rel.tclosure R))))
(assert (distinct b c))
(check-sat)
