(set-logic UFLIA)
(define-fun f ((x Int)) Int (ite (= x 3) 4 5))
(declare-fun g (Int) Int)

(assert (= (g 5) (f 5)))

(check-sat)
(get-value ((f 4)))
(get-value (g))
(get-value (f))
