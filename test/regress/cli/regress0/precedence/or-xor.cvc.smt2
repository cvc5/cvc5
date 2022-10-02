; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () Bool)
(declare-fun B () Bool)
(declare-fun C () Bool)
(check-sat-assuming ( (not (let ((_let_1 (or (xor A B) C))) (let ((_let_2 (xor (or A B) C))) (and (= _let_2 _let_2) (= _let_1 _let_1))))) ))
