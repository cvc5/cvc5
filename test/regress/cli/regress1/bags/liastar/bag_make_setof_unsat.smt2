; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun x () Int)
; the intersection is a constructed bag, so it has one distinct element, and
; the cardinality of its setof is 1. Without concentrating the count of
; (bag x 4) on one element, its 4 occurrences could be spread over 4 distinct
; elements and this would look satisfiable.
(assert (= (bag.inter_min A B) (bag x 4)))
(assert (> (bag.card (bag.setof (bag.inter_min A B))) 1))
(check-sat)
