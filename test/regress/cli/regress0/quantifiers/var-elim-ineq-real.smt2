; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun P (Real) Bool)
(assert (forall ((y Real) (x Real) (z Real)) (or (> (* 3 x) (+ y z)) (not (<= x b)) (= (* 2 x) a) (P y) (P z))))
(assert (not (P 0.0)))
(check-sat)
