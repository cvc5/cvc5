(set-logic LRA)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Real)) (> y x))))
(check-sat)
