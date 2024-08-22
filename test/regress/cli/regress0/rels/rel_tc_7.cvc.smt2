; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= y (rel.join (rel.tclosure x) x)))
(assert (set.member (tuple 1 2) (rel.join (rel.join x x) x)))
(assert (not (set.subset y (rel.tclosure x))))
(check-sat)
