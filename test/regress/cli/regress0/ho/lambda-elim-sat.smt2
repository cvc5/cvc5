; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f (Int) Int)
(assert (= f (lambda ((x Int)) (+ (f 0) x))))
(assert (not (= (f 1) (f 0))))
(check-sat)
(exit)
