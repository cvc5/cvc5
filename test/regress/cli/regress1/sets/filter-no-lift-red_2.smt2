; EXPECT: sat
(set-logic HO_ALL)
(declare-const x Bool)
(declare-const r (Set (Tuple Int)))
(declare-const M (Set (Tuple Int Bool Int Bool Int)))
(assert (distinct (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_36 (Tuple Int))) true) r)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_1 (Tuple Int))) (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_2 (Tuple Int Bool Int Bool Int))) x) M))) r)))
(check-sat)
