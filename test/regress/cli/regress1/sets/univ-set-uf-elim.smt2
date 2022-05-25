; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun f ((Set Bool)) Int)
(declare-fun s () (Set Bool))

(assert (set.member true s))
(assert (set.member false s))
(assert (= a (f (as set.universe (Set Bool)))))

(assert (= (f (as set.empty (Set Bool))) 1))
(assert (= (f (set.singleton true)) 2))
(assert (= (f (set.singleton false)) 3))
(assert (= (f (set.union (set.singleton true) (set.singleton false))) 4))
(check-sat)
