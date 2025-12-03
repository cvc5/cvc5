(assert (and (exists ((? Int)) (and false (exists ((? Int)) (and (forall ((? Int) (? Int)) false)))))))
(check-sat)
