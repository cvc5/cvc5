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

(assert (not (sep (pto x a) (pto y b))))
(assert (sep (pto x a) (pto z b)))

; sat with model where y != z
(check-sat)
