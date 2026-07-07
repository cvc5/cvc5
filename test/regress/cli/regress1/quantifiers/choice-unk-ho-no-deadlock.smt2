; COMMAND-LINE: --mbqi-enum --pre-skolem-quant=on
; EXPECT: unknown
(set-logic HO_ALL)
(declare-sort u 0)
(assert (forall ((E (-> (-> u Bool) u))) (exists ((P (-> u Bool))) (and (exists ((X u)) (not (P X))) (P (E P))))))
(check-sat-assuming ( true ))
