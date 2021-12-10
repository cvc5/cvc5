(set-logic ALL)
(set-info :status sat)
(declare-fun b () (Set (Tuple Int Int)))
(assert 
(= (rel.join b (rel.tclosure (rel.join b b))) (as set.empty (Set (Tuple Int Int))))
)
(assert
(distinct b (as set.empty (Set (Tuple Int Int))))
)
(assert (= (rel.join b b) (as set.empty (Set (Tuple Int Int)))))
(check-sat)
