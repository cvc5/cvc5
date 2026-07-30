; REQUIRES: normaliz
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(set-info :status sat)
(set-option :quiet true)
(declare-const a Int)
(assert (= a (- 5)))
(assert (int.star-contains (lambda ((x Int)) (= x (- 1))) a))
(check-sat)
