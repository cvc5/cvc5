; REQUIRES: normaliz
; DISABLE-TESTER: proof
; Summands are fixed at -2, so the star closure is {0, -2, -4, ...}:
; a positive (and odd) value is unreachable.
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
(declare-const a Int)
(assert (= a 3))
(assert (int.star-contains (lambda ((x Int)) (= x (- 2))) a))
(check-sat)
