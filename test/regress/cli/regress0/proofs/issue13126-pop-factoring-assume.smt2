; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_UF)
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b4 Bool)
(assert (or b4 (not b0)))
(assert (or (not b4) (not b0)))
(assert (or b4 (not b1)))
(assert (or (not b4) b0))
(assert (or b0 b0 b1))
(push)
(assert (or (not b4) (not b0) (not b0)))
(check-sat-assuming (b1 (not b4)))
(pop)
(check-sat)
