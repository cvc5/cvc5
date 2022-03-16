(set-logic LRA)
(set-info :status sat)
(assert (forall ((x Real)) (or (exists ((y Real)) (and (< y 0) (< y x))) (<= x 0))))
(check-sat)
