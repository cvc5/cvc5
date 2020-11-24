; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun s () (Set Int))
(assert (> (card s) 1))
(assert (and (member 0 s) (exists ((x Int)) (member (mod x 1) s))))
(check-sat)
