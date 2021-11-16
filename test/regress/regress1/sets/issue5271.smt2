; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun s () (Set Int))
(assert (> (set.card s) 1))
(assert (and (set.member 0 s) (exists ((x Int)) (set.member (mod x 1) s))))
(check-sat)
