; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int Int) Bool)
(declare-fun k (Int) Int)
(declare-fun A (Int) Bool)
(assert (or (= P Q) (= P R)))
(assert (forall ((x Int) (y Int)) (=> (Q (k x) y) (A (+ x y)))))
(assert (forall ((x Int) (y Int)) (=> (R (k x) y) (A (+ x y)))))
(assert (forall ((z Int)) (=> (A z) (> z 5))))
(assert (P (k 1) 2))
(check-sat)
