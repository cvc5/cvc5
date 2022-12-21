; EXPECT: sat
; EXIT: 0
(set-logic ALL)
(declare-fun x () (Seq Int))
(assert (not (= x (seq.extract x 4 7))))
(check-sat)
