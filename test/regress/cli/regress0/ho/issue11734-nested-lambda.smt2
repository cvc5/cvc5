; EXPECT: sat
(set-logic HO_ALL)
(declare-const lambdaAdd (-> Int (-> Int Int) ))
(assert (= lambdaAdd (lambda ((x Int)) (lambda ((y Int)) (+ x y) ))))
(check-sat)
