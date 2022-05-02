; COMMAND-LINE: --incremental
(set-logic UF)
(set-option :produce-unsat-assumptions true)
(declare-fun _substvar_4_ () Bool)
(check-sat-assuming (_substvar_4_ (= _substvar_4_ _substvar_4_)))
; EXPECT: sat
(check-sat-assuming (_substvar_4_ false))
; EXPECT: unsat
(get-unsat-assumptions)
; EXPECT: (false)
(check-sat-assuming ((= _substvar_4_ _substvar_4_) (distinct _substvar_4_ _substvar_4_)))
; EXPECT: unsat
(get-unsat-assumptions)
; EXPECT: ((distinct _substvar_4_ _substvar_4_))
