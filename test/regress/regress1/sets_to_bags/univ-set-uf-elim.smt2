; COMMAND-LINE: --produce-models
; EXPECT: (error "Extended set operators are not supported in default mode, try --sets-ext.")
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)
(declare-fun f ((Bag Bool)) Int)
(declare-fun s () (Bag Bool))

(assert (bag.count true s))
(assert (bag.count false s))
(assert (= a (f (as set.universe (Bag Bool)))))

(assert (= (f (as bag.empty (Bag Bool))) 1))
(assert (= (f (set.singleton true)) 2))
(assert (= (f (set.singleton false)) 3))
(assert (= (f (bag.union_disjoint (set.singleton true) (set.singleton false))) 4))
(check-sat)
