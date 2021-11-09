; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Set Int))
(assert (= (set.choose A) 10))
(assert (= A (as set.empty (Set Int))))
(check-sat)
