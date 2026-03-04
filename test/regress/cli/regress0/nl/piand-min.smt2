; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (= y 0))
(assert (distinct (piand k x y) 0))
(check-sat)
