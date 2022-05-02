(set-logic ALL)
(set-info :status sat)
(declare-fun b () (Relation Int Int))
(assert 
(= (rel.join b (rel.tclosure (rel.join b b))) (as set.empty (Relation Int Int)))
)
(assert
(distinct b (as set.empty (Relation Int Int)))
)
(assert (= (rel.join b b) (as set.empty (Relation Int Int))))
(check-sat)
