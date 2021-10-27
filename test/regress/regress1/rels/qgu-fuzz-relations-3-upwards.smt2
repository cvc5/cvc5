(set-logic ALL)
(set-info :status sat)
(declare-fun b () (Set (Tuple Int Int)))
(assert 
(= (join b (tclosure (join b b))) (as emptyset (Set (Tuple Int Int))))
)
(assert
(distinct b (as emptyset (Set (Tuple Int Int))))
)
(assert (= (join b b) (as emptyset (Set (Tuple Int Int)))))
(check-sat)
