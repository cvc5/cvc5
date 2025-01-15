; EXPECT: unsat
(set-logic ADTLIRA)
(define-fun i ((y Int)) Bool false)
(define-fun d ((x Int)) Bool (i x))
(assert (exists ((y Int)) (d y)))
(check-sat)
