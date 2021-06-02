(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)

(declare-const a Int)
(declare-const b Int)

(assert (and (sep (pto x a) (or (pto x a) (pto y b)))
       (sep (pto y b) (or (pto x a) (pto y b)))
    )
)

(assert (not (sep (pto x a) (pto y b))))

(check-sat)
