; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Set Int))
(assert (= (choose A) 10))
(assert (= A (as emptyset (Set Int))))
(check-sat)
