; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-info :status sat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const a Int)

(declare-const y Int)
(declare-const b Int)

(assert (or (pto x a) (sep (pto x a) (pto y b))))
(assert (or (not (pto x a)) (sep (not (pto x a)) (not (pto y b)))))

(check-sat)
