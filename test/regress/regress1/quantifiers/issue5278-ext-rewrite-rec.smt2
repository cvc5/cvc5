(declare-datatypes ((a 0)) (((b) (c))))
(define-funs-rec ((d ((x a)) Bool)) ((is-b x)))
(check-sat)
