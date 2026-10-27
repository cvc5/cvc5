; EXPECT: unsat
(set-logic ADTLIRA)
(define-fun i ((x Int)) Bool (or (= x 0) (= x 1)))
(declare-datatypes ((s 0)) (((f))))
(assert (exists ((s s)) (not (i 0))))
(check-sat)
