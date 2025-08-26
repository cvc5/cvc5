(set-logic ALL)
(set-info :status sat)
(set-option :sets-exp true)
(declare-fun x () Int)
(declare-fun y () (Set Int))
(declare-fun P ((Set Int)) Bool)
(assert (= y (as set.universe (Set Int))))
; note that (set.singleton 1) appears in the problem but not in the universe
; set, since no set variable contains the element 1.
(assert (P (set.singleton 1)))
(assert (= (set.inter (as set.universe (Set Int)) (set.singleton 1)) (as set.empty (Set Int))))
(check-sat)
