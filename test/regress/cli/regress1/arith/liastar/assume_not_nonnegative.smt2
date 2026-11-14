; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
(set-logic HO_ALL)
(set-info :status sat)
(declare-const a Int)
(assert (= a (- 5)))
(assert (int.star-contains (lambda ((x Int)) (= x (- 1))) a))
(check-sat)
