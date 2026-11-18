; REQUIRES: unrestricted-mode
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(declare-heap (Bool Bool))
(declare-const b Bool)
(assert (wand (not sep.emp) b))
(check-sat)
