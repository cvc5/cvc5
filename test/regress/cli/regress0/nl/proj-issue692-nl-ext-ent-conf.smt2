; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic QF_NRA)
(set-option :nl-ext-ent-conf true)
(declare-const x Real)
(assert (> 1 (ite (= 0.0 x) (/ x x) (/ (- x) 0.0))))
(check-sat)
