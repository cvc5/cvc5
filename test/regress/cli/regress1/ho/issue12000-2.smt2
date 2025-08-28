; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f (Bool (-> Bool Int)) Bool)
(declare-fun n (Int Bool) (-> Bool (-> Bool Int) Bool))
(declare-fun fn (Bool Bool) Int)
(assert (exists ((x Int)) (distinct f (n (fn true false) false))))
(check-sat)
