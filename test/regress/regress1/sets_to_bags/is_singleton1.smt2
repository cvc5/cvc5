; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Bag Int))
(declare-fun x () Int)
(assert (= (bag.choose (bag x 1)) 5))
(assert (= (bag x 1) S))
(define-fun bag_is_singleton ((B (Bag String))) Bool
  (exists ((x String)) (= B (bag x 1))))
(assert (bag_is_singleton S))
(assert (bag_is_singleton (bag 3 1)))
(check-sat)
