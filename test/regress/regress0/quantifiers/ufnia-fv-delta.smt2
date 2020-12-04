(assert (exists ((k Int)) (not (=> (forall ((a Int) (b Int)) (! (= k (ite (= 0 (mod a 2)) 1 0)) :pattern (b))) false))))
(check-sat)