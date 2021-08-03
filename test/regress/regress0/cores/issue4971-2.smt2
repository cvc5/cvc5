; COMMAND-LINE: --incremental --check-unsat-cores
; EXPECT: sat
(set-logic QF_SLIA)
(assert false)
(reset-assertions)
(check-sat)