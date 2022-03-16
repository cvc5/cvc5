(set-logic ALL)
(set-info :status unsat)
(declare-codatatypes ((list 0)) (((cons (head Int) (tail list)))))

(declare-fun x () list)
(declare-fun y () list)

(assert (= x (cons 0 (cons 0 x))))
(assert (= y (cons 0 y)))
(assert (not (= x y)))
(check-sat)
