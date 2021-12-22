; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Bag Int))
(declare-fun x () Int)
(assert (= (set.choose (bag x)) 5))
(assert (= (bag x) S))
(assert (set.is_singleton S))
(assert (set.is_singleton (bag 3)))
(check-sat)
