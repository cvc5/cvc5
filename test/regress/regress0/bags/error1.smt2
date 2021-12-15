; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun C () (Bag Int))
(declare-fun D () (Bag Int))
(declare-fun E () (Bag Int))
(set-info :status sat)

(assert (= A (bag.union_disjoint D C)))
(assert (not (= A (bag.union_disjoint E A))))

(check-sat)
