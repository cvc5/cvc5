; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)
(declare-fun c () Int)
(assert (forall ((x Int)) (ite (> c 0) (> x 0) (or (< x a) (> x (- a 3))))))
(assert (> c 1))
(check-sat)
