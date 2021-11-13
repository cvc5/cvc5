; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(assert (= (bag.choose A) 10))
(assert (= A (as bag.empty (Bag Int))))
(check-sat)
