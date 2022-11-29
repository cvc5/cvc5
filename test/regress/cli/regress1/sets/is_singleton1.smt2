; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Set Int))
(declare-fun x () Int)
(assert (= (set.choose (set.singleton x)) 5))
(assert (= (set.singleton x) S))
(assert (set.is_singleton S))
(assert (set.is_singleton (set.singleton 3)))
(check-sat)
