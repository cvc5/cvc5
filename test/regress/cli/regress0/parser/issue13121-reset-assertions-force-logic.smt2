; COMMAND-LINE: --incremental --force-logic=QF_UFLIA
; EXPECT: sat
; EXPECT: sat
(declare-const p Bool)
(reset-assertions)
; p is no longer declared after the reset-assertions
(declare-const p Bool)
(declare-const x Int)
(assert (and p (> x 0)))
(check-sat)
(reset)
; ignored since the logic is forced
(set-logic QF_UF)
(declare-const p Bool)
(reset-assertions)
(declare-const p Bool)
(declare-const x Int)
(assert (and p (> x 0)))
(check-sat)
