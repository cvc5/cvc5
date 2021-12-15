; EXPECT: sat
(set-option :incremental false)
(set-option :fmf-bound true)
(set-logic ALL)
(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun z () (Bag Int))
(assert (let ((_let_1 (bag.card y))) (and (> (bag.card x) _let_1) (> _let_1 (bag.card z)))))
(check-sat)
