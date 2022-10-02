; COMMAND-LINE: --full-saturate-quant -i
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(set-option :pre-skolem-quant on)
(declare-fun v7 () Bool)
(assert (forall ((q49 Bool) (q55 Bool)) (xor v7 (exists ((q49 Bool)) (xor v7 q49 q49)) v7 (= q55 q49))))
(check-sat)
