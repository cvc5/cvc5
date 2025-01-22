; EXPECT: unsat
(set-logic ALL)
(assert (= (set.inter (set.union (set.singleton 1) (set.singleton 2)) (set.singleton 1)) (set.minus (set.singleton 3) (set.singleton 4))))
(check-sat)
