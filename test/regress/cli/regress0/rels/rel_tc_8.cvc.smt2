; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (set.member (tuple 2 2) (rel.tclosure x)))
(assert (= x (as set.empty (Relation Int Int))))
(check-sat)
