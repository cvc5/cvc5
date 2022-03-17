; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun w () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (set.member (tuple 1 x) w))
(assert (set.member (tuple y 2) z))
(assert (not (set.member (tuple 1 2) (rel.join w z))))
(check-sat)
