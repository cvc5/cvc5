; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int Int) Bool)
(declare-fun f (Int) Int)

(assert (or (= P Q) (= P R)))

(assert (forall ((x Int) (y Int)) (not (Q (f x) y))))
(assert (forall ((x Int) (y Int)) (not (R (f x) y))))


(assert (P (f 1) 0))
(check-sat)

