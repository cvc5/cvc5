(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))

(define-fun-rec len ((x Lst)) Int (ite ((_ is cons) x) (+ 1 (len (tail x))) 0))

(assert (= (len (cons 0 nil)) 0))
(check-sat)
