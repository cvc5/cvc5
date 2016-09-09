(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (sep (pto x a) true)
        (sep (pto y (+ a 1)) true)
))
(assert (= x y))

(check-sat)
