; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Bag Int))
(define-fun bag_is_singleton ((B (Bag String))) Bool
  (exists ((x String)) (= B (bag x 1))))
(assert
  (bag_is_singleton
    (bag.difference_remove (as set.universe (Bag Int))
                           (bag.difference_remove (as set.universe (Bag Int)) S))))
(assert (= 2 (bag.card S)))
(check-sat)