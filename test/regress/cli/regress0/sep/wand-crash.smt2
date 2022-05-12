; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (wand sep.emp sep.emp))
(check-sat)
