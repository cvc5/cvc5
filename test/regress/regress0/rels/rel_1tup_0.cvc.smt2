; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int)))
(declare-fun z () (Set (Tuple Int)))
(declare-fun b () (Tuple Int Int))
(assert (= b (tuple 2 1)))
(assert (member b x))
(declare-fun a () (Tuple Int))
(assert (= a (tuple 1)))
(assert (member a y))
(declare-fun c () (Tuple Int))
(assert (= c (tuple 2)))
(assert (= z (join x y)))
(assert (not (member c z)))
(check-sat)
