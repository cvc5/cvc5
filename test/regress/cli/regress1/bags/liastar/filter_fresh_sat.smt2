; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the elements mode introduces the two elements of A as terms, and the theory
; makes them falsify the predicate of the filter
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(assert (= (bag.card A) 2))
(assert (= (bag.card (bag.filter (lambda ((x Int)) (>= x 0)) A)) 0))
(check-sat)
