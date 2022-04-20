; REQUIRES: poly
(set-logic NRA)
(set-info :status sat)
(assert (exists ((skoY Real)) (forall ((skoX Real)) (or (= 0.0 (* skoY skoY)) (and (< skoY 0.0) (or (= skoY skoX) (= 2 (* skoY skoY))))))))
(check-sat)
