; COMMAND-LINE: --strings-exp
;EXPECT: sat
(set-logic ALL)
(declare-fun s () (Seq Int))
(assert (= 5 (seq.nth s 5)))
(assert (= 2 (seq.len s)))
(check-sat)
