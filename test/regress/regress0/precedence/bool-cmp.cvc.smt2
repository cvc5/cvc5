; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(check-sat-assuming ( (not (let ((_let_1 (or (and (> x y) (= y z)) (< x z)))) (= _let_1 _let_1))) ))
