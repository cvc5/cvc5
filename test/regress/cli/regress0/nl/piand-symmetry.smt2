; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (distinct (piand k x y) (piand k y x)))
(check-sat)
