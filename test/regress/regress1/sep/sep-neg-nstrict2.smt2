; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)

(assert (not (= a b)))
(assert (not (sep true (pto x b))))
(assert (sep (pto x a) (pto z b)))


(check-sat)
