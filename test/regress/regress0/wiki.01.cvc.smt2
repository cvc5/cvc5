; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(check-sat-assuming ( (not (= (or a (or b c)) (or (or a b) c))) ))
