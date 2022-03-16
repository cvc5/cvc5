(set-logic ALL)

(set-info :status sat)

(declare-fun A () (Bag (Tuple Int Int Int)))
(declare-fun B () (Bag (Tuple Int Int Int)))
(declare-fun C () (Bag (Tuple Int Int Int Int Int Int)))

(assert (= C (table.product A B)))

(declare-fun x () (Tuple Int Int Int))
(declare-fun y () (Tuple Int Int Int))
(declare-fun z () (Tuple Int Int Int Int Int Int))

(assert (bag.member x A))
(assert (bag.member y B))
(assert (bag.member z C))

(assert (distinct x y ((_ tuple_project 0 1 2) z) ((_ tuple_project 3 4 5) z)))

(check-sat)
