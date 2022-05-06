(set-logic ALL)
(set-info :status unsat)

(define-funs-rec ((is-even ((x Int)) Bool) (is-odd ((x Int)) Bool)) ((or (= x 0) (is-odd (- x 1))) (and (not (= x 0)) (is-even (- x 1)))))

(assert (is-even 5))
(check-sat)
