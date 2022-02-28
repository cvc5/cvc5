; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic QF_SLIA)
(assert false)
(reset-assertions)
(check-sat)