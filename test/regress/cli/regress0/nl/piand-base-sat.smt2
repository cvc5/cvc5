; EXPECT: sat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (> k 0))
(assert (= (piand k 0 0) 0))
(check-sat)
