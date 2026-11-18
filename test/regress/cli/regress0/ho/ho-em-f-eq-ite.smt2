; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun F (Int Int) Int)
(declare-fun G (Int Int) Int)
(declare-fun H (Int Int) Int)
(declare-fun k (Int) Int)
(declare-fun b () Bool)
(assert (= F (ite b G H)))
(assert (forall ((x Int) (y Int)) (> (G (k x) y) y)))
(assert (forall ((x Int) (y Int)) (> (H (k x) y) y)))
(assert (= (F (k 3) 4) 0))
(check-sat)
