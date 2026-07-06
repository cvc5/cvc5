; REQUIRES: normaliz
; Tests that a constant lambda, which the rewriter normalizes to a function
; array constant, is handled by the liastar extension.
(set-logic HO_ALL)
(set-info :status sat)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)
(assert (int.star-contains (lambda ((x Int) (y Int)) (and (= x 0) (= y 0))) a b))
(check-sat)
