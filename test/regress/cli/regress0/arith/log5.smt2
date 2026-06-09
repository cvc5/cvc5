;EXPECT: sat
(set-logic ALL)
(declare-const x Int)
(assert (= (int.log2 16) x))
(assert (< x 100))
(check-sat)
