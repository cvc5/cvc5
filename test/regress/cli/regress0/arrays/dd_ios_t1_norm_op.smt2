; EXPECT: unsat
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (= (store a (+ i 2) 0) (store (store (store (store (store (store a (+ i 3) 0) (+ i 2) 1) (+ i 1) 0) i 0) (+ i 5) 0) i 0)))
(check-sat)
