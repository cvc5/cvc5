; EXPECT: unsat
(set-logic ALL)
(declare-const x9 Bool)
(declare-const x Int)
(declare-const x1 Int)
(assert (exists ((a Int)) (and (exists ((s Int)) (and (exists ((a Int)) (and (forall ((o Bool)) (not (ite x9 (forall ((k Int)) true) (= o (= 0 (ite x9 x x1)))))))))))))
(check-sat)
