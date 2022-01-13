; COMMAND-LINE: -q
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ABVNRAT)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (ite (= 0.0 real.pi) false (= (= x (- y)) (= 0.0 (/ 0.0 z 0.0)))))
(check-sat)

(reset)

(set-logic NRAT)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (ite (= 0.0 real.pi) false (= (= x (- y)) (= 0.0 (/ 0.0 z 0.0)))))
(check-sat)

(reset)

(set-logic QF_NRAT)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (ite (= 0.0 real.pi) false (= (= x (- y)) (= 0.0 (/ 0.0 z 0.0)))))
(check-sat)
