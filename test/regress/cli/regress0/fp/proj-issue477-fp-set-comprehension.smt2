; EXPECT: unknown
(set-logic ALL)
(set-option :strings-exp true)
(set-option :sets-ext true)
(assert (= (seq.nth (seq.unit false) (bag.count (_ NaN 11 53) (bag (_ +zero 11 53) 1))) (seq.nth (seq.extract (seq.unit false) (bag.count (_ NaN 11 53) (bag (_ +zero 11 53) 1)) (bag.count (set.choose (set.comprehension ((_x14 Float64)) false _x14)) (bag (_ +zero 11 53) 1))) 0)))
(check-sat)
