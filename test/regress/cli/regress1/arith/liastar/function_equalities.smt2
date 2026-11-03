; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; Two different lambdas of the same type are function-typed shared terms of
; arithmetic. Theory combination asserts the equalities between them, or with
; another function term, to arithmetic as well, which must ignore them: they
; are not arithmetic constraints. Here S1 = {2}, S2 = {3} and a = b = 6.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(declare-const f (-> Int Bool))
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (int.star-contains (lambda ((x Int)) (= x 3)) b))
(assert (or (= f (lambda ((x Int)) (= x 2))) (= f (lambda ((x Int)) (= x 3)))))
(assert (f 3))
(assert (= a b))
(assert (>= a 1))
(assert (<= a 7))
(check-sat)
