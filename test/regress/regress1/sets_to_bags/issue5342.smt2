; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Bag Int))
(define-fun bag_is_singleton ((B (Bag String))) Bool
  (exists ((x String)) (= B (bag x 1))))
(assert (bag_is_singleton (set.complement (set.complement S))))
(assert (= 2 (bag.card S)))
(check-sat)