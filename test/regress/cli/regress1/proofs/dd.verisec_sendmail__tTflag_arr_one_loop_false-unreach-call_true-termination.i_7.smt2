; EXPECT: unsat
(set-logic ALL)
(declare-fun m () Int)
(declare-fun a () Int)
(assert (or (forall ((v Int) (v_ Int)) (or (= 0 (mod v 0)) (= 0 (mod v_ 0)) (= 1 (mod v_ 0)) (= 1 (mod v 0)) (= 1 (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0)))))) (= 1 (mod 0 (+ 1 (mod v 0) (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0)))))))) (= 0 (mod 0 (+ 1 (mod v 0) (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0))))))))))))
(assert (exists ((v Int) (v_ Int)) (and (distinct 0 (mod v 0)) (distinct 0 (mod v_ 0)) (distinct 1 (mod v_ 0)) (distinct 1 (mod v 0)) (distinct 1 (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0)))))) (distinct 0 (mod 0 (+ 1 (mod v 0) (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0)))))))) (distinct 1 (mod 0 (+ 1 (mod v 0) (mod 0 (+ 1 (mod v_ 0) (mod 0 (+ 1 a (mod m 0)))))))))))
(check-sat)
