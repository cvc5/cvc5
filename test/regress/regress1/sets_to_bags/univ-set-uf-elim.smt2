; COMMAND-LINE: --produce-models
; EXPECT: (error "Extended set operators are not supported in default mode, try --sets-ext.")
; EXIT: 1
(set-logic ALL)

(declare-fun a () Int)
(declare-fun f ((Bag Bool)) Int)
(declare-fun s () (Bag Bool))

(define-fun bag.member ((e Bool) (B (Bag Bool))) Bool (>= (bag.count e B) 1))

(assert (bag.member true s))
(assert (bag.member false s))
(assert (= a (f (as set.universe (Bag Bool)))))

(assert (= (f (as bag.empty (Bag Bool))) 1))
(assert (= (f (bag true 1)) 2))
(assert (= (f (bag false 1)) 3))
(assert (= (f (bag.union_disjoint (bag true 1) (bag false 1))) 4))

(check-sat)
