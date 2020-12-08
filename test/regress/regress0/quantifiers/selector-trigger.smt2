(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((T 0)) (
  ((Z) (Y (y Int)))))

(declare-fun b () T)
(declare-fun a () Int)

(declare-fun P (Int) Bool)
(assert (P (y b)))

(assert (forall ((x T)) (not (P (y x)))))

(check-sat)
