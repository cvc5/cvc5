; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun x () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (> (pow2 x) 0))

(check-sat)
