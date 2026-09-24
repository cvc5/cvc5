; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
; the number of distinct elements of A cannot exceed its cardinality
(assert (> (bag.card (bag.setof A)) (bag.card A)))
(check-sat)
