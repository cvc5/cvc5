; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic QF_UF)
(declare-const q Bool)
(reset)
(set-logic QF_UF)
(declare-const p Bool)
(reset-assertions)
; p is no longer declared after the reset-assertions
(declare-const p Bool)
(assert p)
(check-sat)
