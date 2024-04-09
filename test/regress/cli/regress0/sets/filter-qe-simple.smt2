; COMMAND-LINE: --uf-ho-lambda-qe
; EXPECT: sat
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun S () (Set Int)
(assert (not (= (set.filter (lambda ((x Int)) (< x a)) S) (set.filter (lambda ((x Int)) (< x a)) S))))
(check-sat)
