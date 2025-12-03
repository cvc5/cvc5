; EXPECT: unsat
(set-logic ALL)
(declare-fun s (Int Int) Int)
(declare-fun I (Int) Int)
(assert (and (exists ((L Int)) (and (not true) (exists ((? Int)) (and (forall ((R Int)) (or (forall ((? Int)) (or (forall ((? Int)) (= R (s 0 0))))) (and (forall ((? Int)) (= 0 (I ?))) (forall ((? Int)) (! (= (s R 0) (s 0 0)) :pattern ((s 0 0)))))))))))))
(check-sat)
