; COMMAND-LINE:
; EXPECT: sat
(set-logic LIRA)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Int)) (and (>= y x) (< y (+ x 1))))))
(check-sat)
