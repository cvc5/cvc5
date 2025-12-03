; EXPECT: sat
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun f ((-> (-> U Int) (-> Int U) (-> Bool U)) (-> (-> U U) Int)) Bool)
(declare-fun n ((-> (-> U Int) (-> Int U) (-> Bool U)) (-> (-> U U) Int)) Bool)
(assert (distinct f n))
(check-sat)
