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
(assert (= (f (bag true)) 2))
(assert (= (f (bag false)) 3))
(assert (= (f (bag.union_disjoint (bag true) (bag false))) 4))
(check-sat)
