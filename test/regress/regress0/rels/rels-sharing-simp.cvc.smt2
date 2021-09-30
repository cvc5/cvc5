; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun w () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (member (tuple 1 x) w))
(assert (member (tuple y 2) z))
(assert (not (member (tuple 1 2) (join w z))))
(check-sat)
