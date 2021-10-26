; COMMAND-LINE: -i
; EXPECT: sat
(set-logic NIRA)
(push)
(assert (exists ((q29 Int) (q30 Bool) (q35 Bool)) (= (= 0 q29) (= q35 q30))))
(push)
(pop)
(pop)
(check-sat)
