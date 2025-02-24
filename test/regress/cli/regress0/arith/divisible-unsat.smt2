; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(assert ((_ divisible 14) x))
(assert (not ((_ divisible 7) x)))
(check-sat)
