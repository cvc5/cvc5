; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Set Int))
(declare-fun x () Int)
(assert (= (choose (singleton x)) 5))
(assert (= (singleton x) S))
(assert (is_singleton S))
(assert (is_singleton (singleton 3)))
(check-sat)
