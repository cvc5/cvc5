; EXPECT: unsat
; due to unsupported /_total, mod_total operators
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x Int)
(declare-const y Real)
(declare-const z Int)
(assert (or
(not (= (abs x) (ite (< x 0) (- x) x)))
(not (= (abs y) (ite (< y 0.0) (- y) y)))
(not (= (/_total x 0) 0))
(not (= (mod_total z 0) z))
(not (= (to_real y) y))
))
(check-sat)
