; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the models are right (--check-models accepts them), but --debug-check-models
; cannot evaluate a star atom whose arguments are count terms
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag String))
; the rows of the known elements 1 and "a" are 0 in the slots of the other
; element type, and the two fresh elements of B must be strings
(assert (= (bag.count 1 A) 1))
(assert (= (bag.card A) 1))
(assert (= (bag.count "a" B) 1))
(assert (= (bag.card B) 3))
(assert (= (bag.card (bag.setof B)) 3))
(check-sat)
