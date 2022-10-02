; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic UF)
(push 1)
(declare-fun _substvar_4_ () Bool)
(assert _substvar_4_)
(assert _substvar_4_)
(check-sat)
