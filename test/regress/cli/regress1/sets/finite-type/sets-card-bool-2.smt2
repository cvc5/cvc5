(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(set-option :sets-exp true)
(declare-fun A () (Set Bool))
(declare-fun universe () (Set Bool))
(assert (= (set.card A) 2))
(assert (= universe (as set.universe (Set Bool))))
(check-sat)

