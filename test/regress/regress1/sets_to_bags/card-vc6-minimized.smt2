; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun c () (Bag Int))
(declare-fun alloc0 () (Bag Int))
(declare-fun alloc1 () (Bag Int))
(declare-fun alloc2 () (Bag Int))
(assert
 (and (>= (bag.count x c) 1)
      (<= (bag.card (bag.difference_remove alloc1 alloc0)) 1)
      (<= (bag.card (bag.difference_remove alloc2 alloc1))
          (bag.card (bag.difference_remove c (bag x 1))))
      (> (bag.card (bag.difference_remove alloc2 alloc0)) (bag.card c))))
(check-sat)
