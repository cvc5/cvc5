; COMMAND-LINE: --incremental --produce-unsat-cores
; EXPECT: sat
(set-logic QF_SLIA)
(assert false)
(reset-assertions)
(check-sat)
