; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun d () Int)
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () (Set Int))

(assert (= e (set.union b e)))
(assert (= (set.card b) d))
(assert (= (set.card c) 0))
(assert (= 0 (mod 0 d)))
(assert (> (set.card (set.minus e (set.inter (set.inter e b) (set.minus e c)))) 1))

(check-sat)
