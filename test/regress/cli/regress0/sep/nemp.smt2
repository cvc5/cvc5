; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic QF_SEP_LIA)
(declare-heap (Int Int))
(assert (not sep.emp))
(check-sat)
