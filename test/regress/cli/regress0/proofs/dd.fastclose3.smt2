; EXPECT: unsat
(set-logic ALL)
(declare-fun s (Int Int) Int)
(declare-fun I (Int) Int)
(assert (exists ((L Int)) (and (not true) (exists ((? Int)) (forall ((R Int)) (or (forall ((? Int)) (forall ((? Int)) (= R (s 0 0)))) (and (forall ((? Int)) (= 0 (I ?))) (forall ((? Int)) (! (= (s R 0) (s 0 0)) :pattern ((s 0 0)))))))))))
(check-sat)
