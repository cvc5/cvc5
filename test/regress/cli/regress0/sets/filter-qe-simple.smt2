; COMMAND-LINE: --uf-lambda-qe -q
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun S () (Set Int))
(assert (not (= (set.filter (lambda ((x Int)) (< x a)) S) (set.filter (lambda ((x Int)) (< x b)) S))))
(check-sat)
