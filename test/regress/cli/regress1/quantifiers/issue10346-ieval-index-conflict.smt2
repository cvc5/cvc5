; EXPECT: unsat
(set-logic ALIA)
(declare-fun j () Int)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (and (< 0 i) (= 0 (select a 0)) (or (forall ((V Int)) (or (> 0 V) (forall ((? Int)) (or (= 1 ?) (= (select a V) (select a ?))))))) (or (and (exists ((? Int)) (and (exists ((V Int)) (and (<= (+ i 1) V) (> 0 (select (store a 0 (select a j)) V))))))) (exists ((V Int)) (and (exists ((? Int)) (and (<= i ?) (> (select a ?) (select a i)))))))))
(check-sat)
