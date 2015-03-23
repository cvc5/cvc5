(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(define-fun-rec len ((x Lst)) Int (ite (is-cons x) (+ 1 (len (tail x))) 0))

(assert (= (len (cons 0 nil)) 0))
(check-sat)