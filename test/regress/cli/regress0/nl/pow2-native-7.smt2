; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= 7 x))
(assert (>= 9 x))
(assert (> (* 2 (* x x)) (int.pow2 x)))

(check-sat)
