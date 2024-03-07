; EXPECT: sat
(set-logic HO_ALL)
(declare-const a (Table Int Int))
(declare-const b (Table Int))
(define-fun p ((t (Tuple Int Int Int))) Bool (= ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
(assert (= ((_ table.project 0) (table.product a b)) ((_ table.project 0) (bag.filter p (table.product a b)))))
(check-sat)
