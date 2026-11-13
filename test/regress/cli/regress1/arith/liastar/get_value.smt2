; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; EXPECT: sat
; EXPECT: ((a 4) (b 3) ((int.star-contains (lambda ((x Int)) (= x 2)) a) true) ((int.star-contains (lambda ((x Int)) (= x 2)) b) false))
; The model cannot decide whether 4 or 3 is in {2}*, since neither is in
; {2}, so the star atoms take the values of their asserted literals.
(set-logic HO_ALL)
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (not (int.star-contains (lambda ((x Int)) (= x 2)) b)))
(assert (and (> a 3) (< a 5) (> b 2) (< b 4)))
(check-sat)
(get-value (a b (int.star-contains (lambda ((x Int)) (= x 2)) a) (int.star-contains (lambda ((x Int)) (= x 2)) b)))
