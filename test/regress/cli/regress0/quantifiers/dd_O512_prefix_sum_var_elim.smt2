; EXPECT: unsat
(set-logic ALL)
(declare-const x9 Bool)
(declare-const x Int)
(declare-const x1 Int)
(assert (exists ((a Int)) (exists ((s Int)) (exists ((a Int)) (forall ((o Bool)) (not (ite x9 (forall ((k Int)) true) (= o (= 0 (ite x9 x x1))))))))))
(check-sat)
