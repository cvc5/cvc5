(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

(assert (or (forall ((x Int)) (P x)) (forall ((x Int)) (Q x))))

(check-sat)
