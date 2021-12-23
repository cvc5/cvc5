; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Bag Int))
(declare-fun x () Int)
(assert (= (bag.choose (bag x 1)) 5))
(assert (= (bag x 1) S))
(assert (bag.is_singleton S))
(assert (bag.is_singleton (bag 3 1)))
(check-sat)
