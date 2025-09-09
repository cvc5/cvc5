; EXPECT: sat
(set-logic HO_ALL)
(declare-fun x () (Nullable Int))
(declare-fun y () (Nullable Int))
(declare-fun z () (Nullable Int))
(declare-fun f (Int Int) Int)
(assert (distinct x y z))
(assert (= z ((_ nullable.lift f) x y)))
(check-sat)
