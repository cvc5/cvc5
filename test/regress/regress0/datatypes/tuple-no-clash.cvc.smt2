; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)
(declare-fun x () (Tuple Real Real))
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (= x (mkTuple y z)) (= x (mkTuple z y))))
(assert (let ((_let_1 1.0)) (let ((_let_2 0.0)) (or (= x (mkTuple _let_2 _let_2)) (= x (mkTuple _let_1 _let_1))))))
(check-sat)
