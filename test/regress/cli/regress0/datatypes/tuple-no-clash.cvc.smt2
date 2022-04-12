; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)
(declare-fun x () (Tuple Real Real))
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (= x (tuple y z)) (= x (tuple z y))))
(assert (let ((_let_1 1.0)) (let ((_let_2 0.0)) (or (= x (tuple _let_2 _let_2)) (= x (tuple _let_1 _let_1))))))
(check-sat)
