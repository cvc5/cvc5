(set-logic ALL)
(set-info :status unsat)
(set-option :rels-exp true)

(declare-fun R () (Set (Tuple Int Int))) 
(declare-fun x () Int)

(assert (set.member (tuple x x) (rel.tclosure R)))
(assert (rel.acyclic R))
(check-sat)