(declare-const x1 Bool)
(declare-const x Int)
(assert (ite (= 3 (* x (ite (< x 1) x 0))) true x1))
(check-sat)
