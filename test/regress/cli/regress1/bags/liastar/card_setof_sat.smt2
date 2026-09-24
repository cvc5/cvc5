; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values, so the model of a
; sat answer does not satisfy the cardinality constraints yet
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
; A may have duplicates
(assert (< (bag.card (bag.setof A)) (bag.card A)))
(check-sat)
