; COMMAND-LINE: --sygus-inst -q
; EXPECT: sat
(set-logic NIRA)
(set-info :status sat)
(assert (forall ((a Int) (b Int)) (or (> a 0) (<= (to_real a) (/ 0.0 (+ 0.5 (to_real b)))))))
(check-sat)
