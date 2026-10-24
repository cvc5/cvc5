; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the two fresh elements of A have to falsify the predicate of the filter, which
; cannot be read off the rows of the star, so the model is marked unsound
; COMMAND-LINE: --bags-to-liastar
; EXPECT: unknown
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(assert (= (bag.card A) 2))
(assert (= (bag.card (bag.filter (lambda ((x Int)) (>= x 0)) A)) 0))
(check-sat)
