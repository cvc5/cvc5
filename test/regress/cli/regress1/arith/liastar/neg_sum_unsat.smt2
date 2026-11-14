; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; Summands are fixed at -2, so the star closure is {0, -2, -4, ...}:
; a positive (and odd) value is unreachable.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const a Int)
(assert (= a 3))
(assert (int.star-contains (lambda ((x Int)) (= x (- 2))) a))
(check-sat)
