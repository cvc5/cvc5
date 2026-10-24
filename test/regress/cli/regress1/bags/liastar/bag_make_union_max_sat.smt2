; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
; sat with x = y, where the union max is (bag x 3). The two constructed bags
; must be allowed to sit on the same element.
(assert (= (bag.card (bag.union_max (bag x 2) (bag y 3))) 3))
(check-sat)
