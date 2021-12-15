; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(define-sort SetInt () (Bag Int))

(declare-fun A () SetInt)
(declare-fun B () SetInt)
(declare-fun x () Int)
(assert (>= (bag.count x (bag.union_disjoint A B)) 1))

(assert (not (>= (bag.count x (bag.inter_min A B)) 1)))
(assert (not (>= (bag.count x (bag.difference_remove A B)) 1)))
;(assert (not (>= (bag.count x (bag.difference_remove B A))))
;(assert (>= (bag.count x B))

(check-sat)
