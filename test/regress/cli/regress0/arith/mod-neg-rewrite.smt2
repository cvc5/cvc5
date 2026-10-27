; EXPECT: unsat
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (not (= (mod x 101) (mod x (- 101)))))
(check-sat)
