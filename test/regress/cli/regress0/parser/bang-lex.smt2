; EXPECT: unsat
(set-logic ALL)
(declare-fun !x () Int)
(assert (> !x 0))
(assert (< !x 0))
(check-sat)
