; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (mod x 2) 0))
(assert (distinct (mod (piand k x y) 2) 0))
(check-sat)
