; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :miniscope-quant off)
(declare-fun i2 () Int)
(declare-fun v6 () Bool)
(declare-sort S2 0)
(assert (exists ((q521 S2)) (exists ((q523 Int)) (exists ((q524 S2)) (forall ((q525 Bool)) (or (= q524 q521) (= q523 (abs i2)) (and v6 (= q525 (= 0 (abs i2))))))))))
(check-sat)
(assert (= 1 (abs i2)))
(check-sat)
