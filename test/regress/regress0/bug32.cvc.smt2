; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert a)
(check-sat-assuming ( (not (or a b)) ))
