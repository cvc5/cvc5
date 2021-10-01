; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () Bool)
(declare-fun B () Bool)
(declare-fun C () Bool)
(check-sat-assuming ( (not (let ((_let_1 (=> (or A B) C))) (= _let_1 _let_1))) ))
