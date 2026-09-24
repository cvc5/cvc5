; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
; sat with a bag of cardinality 3 whose elements add up to 10
(assert (= (bag.card A) 3))
(assert (= (bag.fold (lambda ((x Int) (y Int)) (+ x y)) 0 A) 10))
(check-sat)
