; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f ((-> Int Int)) Int)
(declare-fun g (Int) Int)
(assert (= (f (lambda ((x Int)) (+ 1 (f g)))) 77))
(check-sat)
