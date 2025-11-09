;EXPECT: sat
(set-logic ALL)
(declare-const x Int)
(assert (< x 0))
(assert (= (int.log2 x) 0))
(check-sat)
