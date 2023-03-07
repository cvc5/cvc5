; COMMAND-LINE: --model-cores=simple
; EXPECT: sat
(set-logic ALL)
(assert (exists ((x Int)) (= (div 1 x x) 0)))
(check-sat)
