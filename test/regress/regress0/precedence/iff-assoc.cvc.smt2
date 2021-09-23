; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () Bool)
(declare-fun B () Bool)
(declare-fun C () Bool)
(check-sat-assuming ( (not (= (= (= A B) C) (= A (= B C)))) ))
