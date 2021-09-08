; EXPECT: sat
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun f (Int Int) Int)
(declare-fun g (Int) (-> Int Int))
(declare-fun h () (-> Int Int Int))

(assert (and (= f g) (= g h)))

(assert (= (f 1 2) 5))
(assert (= (f 2 1) 7))

(check-sat)
