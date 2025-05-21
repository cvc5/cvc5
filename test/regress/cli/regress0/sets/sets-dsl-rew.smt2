; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (Set Int))
(assert (or
(not (= (set.inter (as set.empty (Set Int)) x) (as set.empty (Set Int))))
(not (= (set.inter x (as set.empty (Set Int))) (as set.empty (Set Int))))
(not (= (set.minus x (as set.empty (Set Int))) x))
(not (= (set.minus (as set.empty (Set Int)) x) (as set.empty (Set Int))))
))
(check-sat)
