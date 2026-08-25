; EXPECT: sat
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (< x y))
(assert (= (* y y) 4))
(assert (<= (int.pow2 y) (int.pow2 x)))
(check-sat)
