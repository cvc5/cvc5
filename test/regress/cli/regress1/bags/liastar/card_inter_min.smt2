; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
; the intersection cannot be bigger than A
(assert (= (bag.card A) 5))
(assert (= (bag.card (bag.inter_min A B)) 7))
(check-sat)
