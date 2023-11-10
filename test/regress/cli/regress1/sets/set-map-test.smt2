(set-logic HO_ALL)
(set-info :status sat)
(define-fun iabs ((x Int)) Int (ite (< x 0) (- x) x))

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))
(declare-fun x () Int)

(assert (not (= T S)))
(assert (= (set.map iabs T) (set.map iabs S)))

(check-sat)
