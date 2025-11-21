(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Bool) (b Bool)) (exists ((c Bool)) (=> a (and (= c b) (forall ((b Bool)) (= c (and a b))))))))
(check-sat)