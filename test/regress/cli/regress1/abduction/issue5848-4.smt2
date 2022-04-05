; COMMAND-LINE: --produce-abducts
; EXPECT: fail
(set-logic UFLRA)
(declare-sort S0 0)
(declare-fun S0-0 () S0)
(declare-fun S0-1 () S0)
(declare-fun v87 () Bool)
(get-abduct A (and false (exists ((q117 S0)) (or v87 (and (= S0-1 q117) (= q117 S0-0))))))
