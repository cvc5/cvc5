(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((list 0)) (
((cons (head Int) (tail list)) (nil))
))
(declare-fun a () list)
(assert (= ((_ update head) a 3) (cons 3 nil)))
(check-sat)
