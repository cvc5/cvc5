; COMMAND-LINE: --finite-model-find
; EXPECT: unknown
(set-logic AUFLIRA)
(set-info :status unknown)
(declare-fun _substvar_1_ () Int)
(declare-fun tptp_const_array1 (Int Real) (Array Int Real))
(assert (forall ((?I_4 Int) (?L_5 Int) (?U_6 Int) (?Val_7 Real)) (=> true (= (select (tptp_const_array1 _substvar_1_ ?Val_7) 0) ?Val_7))))
(check-sat)