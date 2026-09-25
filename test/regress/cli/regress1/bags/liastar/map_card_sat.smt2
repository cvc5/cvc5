; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the fresh elements the star needs cannot be read back into a bag.map or
; bag.filter term, see BagSolver::collectLiastarModelValues, so the model is
; marked unsound and the answer is unknown, although the problem is sat
; COMMAND-LINE: --bags-to-liastar
; EXPECT: unknown
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(define-fun f ((i Int)) Int 7)
; a constant map sends the 3 occurrences of A to one distinct element
(assert (= (bag.card A) 3))
(assert (= (bag.card (bag.setof (bag.map f A))) 1))
(check-sat)
