; EXPECT: sat

(set-logic ALL)
(set-info :status sat)

(declare-fun t () Tuple)
(declare-fun t1 () (Tuple (Tuple Int Int) (Tuple Int String Int)))
(declare-fun t2 () (Tuple (Tuple Bool Int) String))

(assert (= t1 (tuple (tuple 12 99) (tuple 5 "xyz" 17))))
(assert (= t2 (tuple (tuple true 14) "abc")))
(assert (= t tuple))

(check-sat)
