; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-const x6 Real)
(set-option :produce-unsat-cores true)
(declare-const x Real)
(assert (= x6 (/ x x)))
(assert (> (- x) 0.0))
(assert (> (/ 2 x x) x))
(check-sat)
