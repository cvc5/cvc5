; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; int.star-contains together with nonlinear multiplication. The nonlinear
; extension runs after the liastar extension and must ignore the
; int.star-contains literal and the function-typed shared term it introduces.
; Here S = {2}, so a * b = 8 with b >= 4 forces a = 2.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (= (* a b) 8))
(assert (>= b 4))
(check-sat)
