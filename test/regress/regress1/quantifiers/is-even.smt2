(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(define-funs-rec ((is-even ((x Int)) Int) (is-odd ((y Int)) Int)) ((ite (= x 0) 1 (ite (= (is-odd (- x 1)) 0) 1 0)) (ite (= y 0) 0 (ite (= (is-even (- y 1)) 0) 1 0))))

(assert (= (is-even 4) 0))
(check-sat)
