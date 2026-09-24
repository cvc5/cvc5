; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(define-fun f ((i Int)) Int 7)
; a constant map sends the 3 occurrences of A to one distinct element
(assert (= (bag.card A) 3))
(assert (= (bag.card (bag.setof (bag.map f A))) 1))
(check-sat)
