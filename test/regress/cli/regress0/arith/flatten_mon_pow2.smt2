; EXPECT: unsat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x (int.pow2 x)))
(assert (not (= (* x y) (* (int.pow2 x) y))))
(check-sat)
