; EXPECT: unsat
(set-logic AUFDTLIRA)
(declare-sort ns 0)
(declare-fun n (ns) Int)
(define-fun t ((x ns)) Int (n x))
(declare-const r ns)
(assert (exists ((x (Array Int ns)) (x1 (Array Int ns))) (not (=> (= x (store x1 1 r)) (= x (store (store (store (store (store (store x 2 r) 0 r) 5 r) 3 r) 4 r) 9 r)) (= x (store x 0 r))))))
(check-sat)
