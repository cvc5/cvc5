; EXPECT: sat
(set-logic ALL)
(declare-fun T () Int)
(assert ((_ divisible 3) (mod T 3)))
(check-sat)
