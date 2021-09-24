; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (or x y))
(assert (not (or x y)))
(check-sat)
