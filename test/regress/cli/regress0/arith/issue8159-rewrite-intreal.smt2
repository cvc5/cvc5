; EXPECT: sat
(set-logic QF_LIRA)
(declare-fun a () Real)
(declare-fun b () Int)
(assert (>= a (+ a b)))
(check-sat)
