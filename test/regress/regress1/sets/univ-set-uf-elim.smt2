; EXPECT: (error "Extended set operators are not supported in default mode, try --sets-ext.")
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)
(declare-fun f ((Set Bool)) Int)
(declare-fun s () (Set Bool))

(assert (member true s))
(assert (member false s))
(assert (= a (f (as univset (Set Bool)))))

(assert (= (f (as emptyset (Set Bool))) 1))
(assert (= (f (singleton true)) 2))
(assert (= (f (singleton false)) 3))
(assert (= (f (union (singleton true) (singleton false))) 4))
(check-sat)
