(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (sep (pto x y) (pto y z)))
(assert (and (> x 3) (< x 5)))
(assert (and (> y 3) (< y 5)))
(check-sat)
