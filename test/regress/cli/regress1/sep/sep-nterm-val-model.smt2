(set-logic QF_ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)

(assert (and 
  (not (sep (not (pto x a)) (not (pto y b)) ))
  (sep (pto x (+ a 1)) (pto y (+ b 1)))
  )
)

(check-sat)
