; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (< (str.to_int x) (- 2)))
(check-sat)
