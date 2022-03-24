; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_SEP_LIA)
(declare-heap (Int Int))
(assert (not sep.emp))
(check-sat)
