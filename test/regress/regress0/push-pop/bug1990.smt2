; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_SAT)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(assert (or v1 v2))
(check-sat)
(assert false)
(push)
(check-sat)
(pop)
(check-sat)
