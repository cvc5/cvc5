; REQUIRES: normaliz
; DISABLE-TESTER: proof
; (int.star-contains (lambda ((x Int) (y Int)) (= (+ x y) 2)) 5 0)
; Hilbert basis: {}, maximal subspace: {(1, -1)}
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)
(assert (= a 5))
(assert (= b 0))
(assert (int.star-contains (lambda ((x Int) (y Int)) (= (+ x y) 2)) a b))
(check-sat)
