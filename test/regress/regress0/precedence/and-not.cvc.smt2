; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () Bool)
(declare-fun B () Bool)
(check-sat-assuming ( (not (let ((_let_1 (and A (not B)))) (= _let_1 _let_1))) ))
