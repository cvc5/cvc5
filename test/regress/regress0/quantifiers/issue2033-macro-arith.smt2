; COMMAND-LINE: --macros-quant
; EXPECT: sat
(set-logic AUFNIRA)
(set-info :status sat)
(declare-fun _substvar_4_ () Real)
(declare-sort S2 0)
(declare-sort S10 0)
(declare-fun f22 (S10 S2) Real)
(assert (forall ((?v0 S10) (?v1 S2)) (= _substvar_4_ (- (f22 ?v0 ?v1)))))
(check-sat)
