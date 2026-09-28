; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the fresh elements the star needs cannot be read back into a bag.map or
; bag.filter term by the subsolver mode (which answers unknown here), so the
; elements mode introduces them as terms the theory reasons about. Its model
; is accepted by --check-models; --debug-check-models cannot evaluate a star
; literal a false guard left free
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(define-fun f ((i Int)) Int 7)
; a constant map sends the 3 occurrences of A to one distinct element
(assert (= (bag.card A) 3))
(assert (= (bag.card (bag.setof (bag.map f A))) 1))
(check-sat)
