; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-sort i 0)
(declare-fun i (i) Int)
(assert (exists ((r Int)) (and (not true) (exists ((r Int)) (forall ((j Int)) (forall ((o Bool)) (exists ((j Int)) (exists ((o Int)) (exists ((o Int)) (exists ((p Bool)) (ite p (exists ((o Int)) (exists ((o i)) (= 0 (i o)))) (and x (exists ((o Int)) (exists ((o i)) (= 0 (i o))))))))))))))))
(check-sat)
