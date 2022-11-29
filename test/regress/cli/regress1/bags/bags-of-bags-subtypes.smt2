(set-logic ALL)
(set-info :status sat)

(declare-fun s () (Bag (Bag Real)))
(declare-fun t () (Bag (Bag Real)))

(declare-fun x () (Bag Real))
(declare-fun y () (Bag Real))

(assert (>= (bag.count 0.5 y) 1))
(assert (>= (bag.count y s) 1))
(assert (or (= s t) (= s (bag (bag 1.0 1) 1)) (= s (bag (bag 0.0 1) 1))))

(check-sat)
