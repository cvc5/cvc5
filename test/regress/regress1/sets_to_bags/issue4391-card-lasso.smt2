; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun d () Int)
(declare-fun b () (Bag Int))
(declare-fun c () (Bag Int))
(declare-fun e () (Bag Int))

(assert (= e (bag.union_disjoint b e)))
(assert (= (bag.card b) d))
(assert (= (bag.card c) 0))
(assert (= 0 (mod 0 d)))
(assert (> (bag.card (bag.difference_remove e (bag.inter_min (bag.inter_min e b) (bag.difference_remove e c)))) 1))

(check-sat)
