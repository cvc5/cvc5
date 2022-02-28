(set-logic ALL)
(set-option :incremental true)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun x () (Set Bool))
(declare-fun y () (Set Bool))
(declare-fun z () (Set Bool))
(assert (= x (set.singleton true)))
(assert (= y (set.singleton false)))
(push 1)

(assert (= z (set.complement y)))

(check-sat)

(pop 1)
