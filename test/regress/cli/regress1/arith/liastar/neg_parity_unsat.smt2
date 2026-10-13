; REQUIRES: normaliz
; DISABLE-TESTER: proof
; Summands may be +2 or -2, so the star closure is exactly the even
; integers: an odd value is unreachable in either direction.
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
(declare-const a Int)
(assert (= a 5))
(assert (int.star-contains (lambda ((x Int)) (or (= x 2) (= x (- 2)))) a))
(check-sat)
