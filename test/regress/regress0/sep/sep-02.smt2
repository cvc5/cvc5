(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (sep (pto x a) (pto y b) (pto z c)))

(assert (or (= x y) (= y z) (= x z)))

(check-sat)
