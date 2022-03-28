; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic NRA)
(set-info :status sat)
(set-option :ext-rewrite-quant true)
(assert (exists ((a Real) (b Real)) (forall ((c Real)) (= (/ b (/ 1 c)) 0))))
(check-sat)
