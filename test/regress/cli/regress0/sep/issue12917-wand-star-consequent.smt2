; REQUIRES: unrestricted-mode
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep true (wand sep.emp (sep sep.emp sep.emp))))
(check-sat)
