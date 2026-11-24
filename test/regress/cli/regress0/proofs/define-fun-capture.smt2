; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int) Bool)
(define-fun f ((x Int)) Bool (forall ((y Int)) (P x y)))
(assert (forall ((y Int)) (=> (Q y) (f y))))
(assert (Q 3))
(assert (not (P 3 4)))
(check-sat)
