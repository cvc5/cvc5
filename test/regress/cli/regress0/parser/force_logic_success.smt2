; COMMAND-LINE: --force-logic QF_BV --print-success
; EXPECT: success
; EXPECT: sat
(assert true)
(check-sat)
