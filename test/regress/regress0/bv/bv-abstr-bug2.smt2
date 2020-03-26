; COMMAND-LINE: --solve-int-as-bv=32 
(set-logic QF_NIA)
(set-info :status sat)
(declare-fun _substvar_7_ () Bool)
(declare-fun _substvar_3_ () Int)
(assert (or _substvar_7_ (= 0 _substvar_3_)))
(check-sat)
