; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL)
(set-info :status sat)
(declare-heap (Int Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)

(assert (not (pto x a)))
(assert (sep (pto x a) (pto z b)))

(check-sat)
