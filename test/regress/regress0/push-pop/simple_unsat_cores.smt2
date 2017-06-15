; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
(set-option :produce-unsat-cores true)
(set-logic UF)
(push 1)
(assert false)
(check-sat)
(pop 1)
(assert false)
(check-sat)
