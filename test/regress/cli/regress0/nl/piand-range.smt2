; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (< x (piand k x y)))
(check-sat)
