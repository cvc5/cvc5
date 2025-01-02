; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-const r Real)
(assert (= 1.0 (/ 2 r r)))
(check-sat)
