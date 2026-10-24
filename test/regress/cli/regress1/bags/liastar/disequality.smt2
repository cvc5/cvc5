; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
; both differences are empty, so the two bags are equal. This exercises the
; translation of a negated bag atom.
(assert (= 0 (bag.card (bag.difference_subtract A B))))
(assert (= 0 (bag.card (bag.difference_subtract B A))))
(assert (not (= A B)))
(check-sat)
