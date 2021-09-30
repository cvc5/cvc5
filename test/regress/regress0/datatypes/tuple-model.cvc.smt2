; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (Tuple Int Int))
(assert (= ((_ tuple_select 0) x) 5))
(check-sat)
