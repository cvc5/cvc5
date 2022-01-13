; EXPECT: sat
(set-logic QF_ANRAT)
(declare-const b Bool)
(declare-const x (Array Real Real))
(declare-const y Real)
(assert (or (not b) (= 1.0 (select (store x (- (/ (+ 0.0 real.pi) y)) 0.0) 0.0))))
(check-sat)
