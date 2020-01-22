(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= a b))
(check-sat)
