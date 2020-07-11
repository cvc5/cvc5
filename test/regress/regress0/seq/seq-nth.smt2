;EXPECT: sat
(set-logic ALL)
(declare-fun s () (Seq Int))
(assert (= 5 (seq.nth s 1)))
(check-sat)