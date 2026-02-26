;EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(assert (= (int.log2 x) 5))
(assert (> x 100))
(check-sat)
