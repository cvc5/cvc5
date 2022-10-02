; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-info :status sat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (not (sep (not (pto x a)) (pto y b) ))  
        (sep (pto x a) (pto y b))
  )
)

(check-sat)
