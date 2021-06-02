(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)

(declare-const a Int)
(declare-const b Int)

(assert (and (pto x a) (pto x b)))

(assert (not (= a b)))

(check-sat)
