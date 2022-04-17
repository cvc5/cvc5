(set-logic ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun C () (Bag Int))
(declare-fun D () (Set Int))
(declare-fun E () (Set Int))
(declare-fun F () (Set Int))

(assert (and
(= (bag.union_max A B C) (bag.union_max (bag.union_max A B) C))
(= (bag.union_disjoint A B C) (bag.union_disjoint (bag.union_disjoint A B) C))
(= (bag.difference_subtract A B C) (bag.difference_subtract (bag.difference_subtract A B) C))
(= (set.inter D E F) (set.inter (set.inter D E) F))
(= (set.union D E F) (set.union (set.union D E) F))
(= (set.minus D E F) (set.minus (set.minus D E) F))
))

(check-sat)
