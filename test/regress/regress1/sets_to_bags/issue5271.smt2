; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun s () (Bag Int))
(assert (> (bag.card s) 1))
(assert (and (>= (bag.count 0 s) 1) (exists ((x Int)) (>= (bag.count (mod x 1) s) 1))))
(check-sat)
