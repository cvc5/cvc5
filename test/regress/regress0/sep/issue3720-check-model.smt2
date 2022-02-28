; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(declare-heap (Int Int))
(assert sep.emp)
(check-sat)
