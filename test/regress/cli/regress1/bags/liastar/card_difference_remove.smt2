; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
; bag.difference_remove removes at least as much as bag.difference_subtract
(assert (> (bag.card (bag.difference_remove A B))
           (bag.card (bag.difference_subtract A B))))
(check-sat)
