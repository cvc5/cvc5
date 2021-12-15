(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun C () (Bag Int))
(declare-fun D () (Bag Int))

(assert (>= (bag.count x A) 1))
(assert (>= (bag.count y B) 1))
(assert (or (= C (bag.inter_min A B)) (= D (bag.inter_min A B))))


(check-sat)
