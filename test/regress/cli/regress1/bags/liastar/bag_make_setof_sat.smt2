; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun x () Int)
; sat with A = (bag x 4) and B a superbag of it
(assert (= (bag.inter_min A B) (bag x 4)))
(assert (= (bag.card (bag.setof (bag.inter_min A B))) 1))
(assert (= (bag.card A) 4))
(check-sat)
