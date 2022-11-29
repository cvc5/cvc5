; COMMAND-LINE:
; EXPECT: sat
(set-logic LIRA)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Int)) (and (>= (to_real y) x) (< (to_real y) (+ x 1.0))))))
(check-sat)
