; EXPECT: sat
(set-logic ALL)
(declare-fun i () Int)
(declare-fun t () String)
(declare-fun r () String)
(assert (distinct 0 (str.indexof (str.++ r r) (str.++ t t) (* (abs i) (str.len (str.++ t t))))))
(check-sat)
