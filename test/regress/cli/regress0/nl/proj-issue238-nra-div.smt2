; EXPECT: sat
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (< a b))
(assert (or (< b 0) (= (/ 3 b) 1)))
(check-sat)
