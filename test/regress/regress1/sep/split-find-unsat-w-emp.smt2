(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (not (sep (not (pto x a)) (not (pto y b)) (not (sep (pto x a) (pto y b))) (not (emp x x)) ))
        (sep (pto x a) (pto y b))
  )
)

(check-sat)
