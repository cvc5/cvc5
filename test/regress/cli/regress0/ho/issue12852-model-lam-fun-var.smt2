; COMMAND-LINE: --debug-check-models
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(declare-fun a () (-> Int Int))
(declare-fun b () (-> Int Int))
(assert (= a (lambda ((x Int)) (f (g x)))))
(assert (= b (lambda ((x Int)) (g (f x)))))
(assert (distinct a b))
(check-sat)
