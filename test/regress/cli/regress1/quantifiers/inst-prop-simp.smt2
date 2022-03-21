(set-logic UFLIA)
(set-info :status unsat)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)

(assert (forall ((x Int)) (=> (Q x) (R x))))
(assert (forall ((x Int)) (=> (P x) (not (R x)))))

(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (or (= a b) (= a c)))

(assert (P (f a)))
(assert (Q (f b)))
(assert (Q (f c)))
(check-sat)
