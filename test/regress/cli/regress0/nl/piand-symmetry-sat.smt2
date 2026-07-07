; EXPECT: sat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (piand k x y) y))
(assert (= (piand k y x) y))
(check-sat)
