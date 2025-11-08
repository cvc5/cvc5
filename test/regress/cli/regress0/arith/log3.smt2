;EXPECT: sat
(set-logic ALL)
(assert (= (int.log2 (- 2)) 0))
(check-sat)
