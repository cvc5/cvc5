; EXPECT: unsat
(set-logic ALL)
(assert (= (set.choose (set.union (set.singleton 4) (set.singleton 3))) 2))
(check-sat)
