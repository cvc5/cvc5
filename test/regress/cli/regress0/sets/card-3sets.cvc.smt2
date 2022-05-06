; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(assert (let ((_let_1 (set.card y))) (and (> (set.card x) _let_1) (> _let_1 (set.card z)))))
(check-sat)
