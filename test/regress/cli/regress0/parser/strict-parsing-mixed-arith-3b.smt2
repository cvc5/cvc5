; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_LRA)
; ok since 0 is treated as 0.0 in this logic
(assert (= 0 0.0))
(check-sat)
