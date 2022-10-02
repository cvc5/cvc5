; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () Int)
(declare-fun B () Int)
(check-sat-assuming ( (not (let ((_let_1 (not (= A B)))) (= _let_1 _let_1))) ))
