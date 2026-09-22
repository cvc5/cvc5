; EXPECT: unsat
(set-logic ALL)
(assert (forall ((a Bool) (b Bool)) (exists ((c Bool)) (=> a (and (= c b) (forall ((b Bool)) (= c (and a b))))))))
(check-sat)
