; EXPECT: sat
(set-logic ALL)
(declare-fun x () (Set Int))
(declare-fun t () (Set Int))
(assert (distinct true (= 0 (set.card x))))
(assert (or (forall ((Set Int)) (= 1 (set.card (set.inter (set.inter t t) (set.minus t x)))))))
(check-sat)
