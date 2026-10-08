; REQUIRES: normaliz
; Summands may be +1 or -1, so the star closure is all of Z and any
; value -- here a negative one -- is reachable.
(set-logic HO_ALL)
(set-info :status sat)
(set-option :quiet true)
(declare-const a Int)
(assert (= a (- 7)))
(assert (int.star-contains (lambda ((x Int)) (or (= x 1) (= x (- 1)))) a))
(check-sat)
