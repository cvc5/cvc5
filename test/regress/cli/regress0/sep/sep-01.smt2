(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)

(declare-const a Int)
(declare-const b Int)

(assert (sep (pto x a) (pto y b)))

(assert (= x y))

(check-sat)
