; COMMAND-LINE: --full-saturate-quant -i --no-check-unsat-cores
; EXPECT: unsat
(set-logic ALL)
(set-option :pre-skolem-quant true)
(declare-fun v7 () Bool)
(assert (forall ((q49 Bool) (q55 Bool)) (xor v7 (exists ((q49 Bool)) (xor v7 q49 q49)) v7 (= q55 q49))))
(check-sat)