; EXPECT: sat

(set-logic ALL)
(set-info :status sat)

(declare-fun t () Tuple)
(declare-fun t1 () (Tuple (Tuple Int Int) (Tuple Int String Int)))
(declare-fun t2 () (Tuple (Tuple Bool Int) String))

(assert (= t1 (mkTuple (mkTuple 12 99) (mkTuple 5 "xyz" 17))))
(assert (= t2 (mkTuple (mkTuple true 14) "abc")))
(assert (= t mkTuple))

(check-sat)
