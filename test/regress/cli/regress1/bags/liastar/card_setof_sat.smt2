; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
; A may have duplicates
(assert (< (bag.card (bag.setof A)) (bag.card A)))
(check-sat)
