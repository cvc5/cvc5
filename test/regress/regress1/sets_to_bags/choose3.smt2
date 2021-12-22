; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Bag Int))
(assert (= (set.choose A) 10))
(assert (= A (as bag.empty (Bag Int))))
(check-sat)
