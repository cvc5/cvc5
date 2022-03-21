; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun k (Int Int) Int)

(assert (q (k 0 1)))
(assert (not (p (k 0 0))))

(assert (forall ((f (-> Int Int Int)) (y Int) (z Int)) (or (p (f y z)) (not (q (f 1 y))))))
;solved by instantiating with {f->\lambda w1w2. (k 0 w1), y-> 0, z-> _ }

(check-sat)
(exit)
