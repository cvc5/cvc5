; EXPECT: sat
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= a ((as const (Array Int Int)) 0)))
(assert (distinct b ((as const (Array Int Int)) 1)))
(assert (= (store a 2 3) (store b 2 3)))
(check-sat)
