; EXPECT: unsat
(set-logic ALL)
(assert (= (set.inter (set.union (set.singleton 0) (set.singleton 0)) (set.singleton 1)) (set.singleton 1)))
(check-sat)
