; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= 0 x))
(assert (<= 0 y))
(assert (< x y))
(assert (> (int.pow2 x) (int.pow2 y)))

(check-sat)
