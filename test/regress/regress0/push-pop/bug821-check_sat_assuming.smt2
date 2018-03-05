; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic UF)
(declare-fun _substvar_4_ () Bool)
(check-sat-assuming (_substvar_4_ _substvar_4_))
(check-sat-assuming (_substvar_4_ false))
(check-sat-assuming ((= _substvar_4_ _substvar_4_)))
