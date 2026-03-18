; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x (piand k x y)))
(assert (not (= (* x y) (* (piand k x y) y))))
(check-sat)
