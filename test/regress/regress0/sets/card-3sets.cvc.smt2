; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(assert (let ((_let_1 (card y))) (and (> (card x) _let_1) (> _let_1 (card z)))))
(check-sat)
