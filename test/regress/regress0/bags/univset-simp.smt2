; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun a () (Bag Int))
(declare-fun b () (Bag Int))
(declare-fun c () (Bag Int))
(declare-fun d () (Bag Int))
(declare-fun e () (Bag Int))
(declare-fun f () (Bag Int))

(declare-fun x () Int)

(assert (not (>= (bag.count 0 a) 1)))
(assert (>= (bag.count 0 b) 1))
(assert (not (>= (bag.count 1 c) 1)))
(assert (>= (bag.count 2 d) 1))
(assert (= e (as set.universe (Bag Int))))
(assert (= f (set.complement d)))
(assert (not (>= (bag.count x (as set.universe (Bag Int))) 1)))

(check-sat)
