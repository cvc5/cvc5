(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)


(declare-fun p (Int) Bool)
(declare-fun A () (Set Int))
(declare-fun F () (Set Int))



(assert (= F (insert x y (singleton z))))
(assert (subset F A))
(assert (= x y))


(check-sat)

