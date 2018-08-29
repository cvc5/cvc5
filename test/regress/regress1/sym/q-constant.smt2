(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int Int) Bool)

(assert (or (forall ((x Int)) (R x a)) (forall ((x Int)) (R x b))))

(check-sat)
