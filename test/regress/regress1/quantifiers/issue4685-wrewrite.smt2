; COMMAND-LINE: --sygus-inst --no-check-models
; EXPECT: sat
(set-logic NIRA)
(set-info :status sat)
(assert (forall ((a Int) (b Int)) (or (> a 0) (<= a (/ 0 (+ 0.5 b))))))
(check-sat)
