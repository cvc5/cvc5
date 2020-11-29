; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun d () Int)
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () (Set Int))

(assert (= e (union b e)))
(assert (= (card b) d))
(assert (= (card c) 0))
(assert (= 0 (mod 0 d)))
(assert (> (card (setminus e (intersection (intersection e b) (setminus e c)))) 1))

(check-sat)
