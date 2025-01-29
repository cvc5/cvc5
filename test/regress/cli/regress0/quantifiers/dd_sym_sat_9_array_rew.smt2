; EXPECT: unsat
(set-logic ALL)
(declare-const x (Array Int (Array Int Real)))
(declare-fun s ((Array Int (Array Int Real)) Int) Bool)
(declare-fun a () (Array Int (Array Int Real)))
(assert (forall ((n Int) (?a (Array Int (Array Int Real)))) (= (s ?a 0) (forall ((? Int)) (or (= 1 n) (= (select (select ?a ?) 1) (select (select x 1) 0)))))))
(assert (not (s (store (store (store (store (store (store (store x 1 (store (select x 1) 1 0.0)) 0 (select a 0)) 3 (select x 1)) 2 (select x 0)) 5 (select x 0)) 6 (select x 0)) 7 (select x 1)) 0)))
(check-sat)
