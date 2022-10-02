; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun p (Int) Bool)
(declare-fun g (Int) Int)

(assert (not (p (g 0))))
;(assert (= 0 (g 0)))

(assert (forall ((f (-> Int Int)) (y Int)) (p (f (f (f (f (f y))))))))

(check-sat)
(exit)
