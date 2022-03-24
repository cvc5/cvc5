; COMMAND-LINE: --sep-pre-skolem-emp
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (not sep.emp))
(check-sat)
