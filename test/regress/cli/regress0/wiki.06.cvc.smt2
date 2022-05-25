; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(check-sat-assuming ( (not (= (and a (or a b)) a)) ))
