; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic UF)
(set-option :produce-unsat-assumptions true)
(declare-fun _substvar_4_ () Bool)
(check-sat-assuming (_substvar_4_ (= _substvar_4_ _substvar_4_)))
(check-sat-assuming (_substvar_4_ false))
(get-unsat-assumptions)
(check-sat-assuming ((= _substvar_4_ _substvar_4_) (distinct _substvar_4_ _substvar_4_)))
(get-unsat-assumptions)
