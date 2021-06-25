; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (<= x y))
(assert (> (pow2 x) (pow2 y)))

(check-sat)
