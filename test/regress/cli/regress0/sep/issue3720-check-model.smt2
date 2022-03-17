; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(declare-heap (Int Int))
(assert sep.emp)
(check-sat)
