(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-codatatypes () ((list (cons (head Int) (tail list)))))

(declare-fun x () list)
(declare-fun y () list)

(assert (= x (cons 0 (cons 0 x))))
(assert (= y (cons 0 y)))
(assert (not (= x y)))
(check-sat)
