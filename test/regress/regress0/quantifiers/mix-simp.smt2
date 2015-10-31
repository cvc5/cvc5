(set-logic ALL_SUPPORTED)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Int)) (and (>= y x) (< y (+ x 1))))))
(check-sat)
