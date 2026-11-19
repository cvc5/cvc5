; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (Tuple Int Int))
(assert (= ((_ tuple.select 0) x) 1))
(assert (= ((_ tuple.select 1) x) 2))
(assert (not (= x (tuple 1 2))))
(check-sat)
