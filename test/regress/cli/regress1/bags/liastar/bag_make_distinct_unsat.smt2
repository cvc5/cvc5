; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
; distinct elements make the two constructed bags disjoint, so the union max
; has cardinality 2 + 3, and 3 would need x and y to be equal
(assert (not (= x y)))
(assert (= (bag.card (bag.union_max (bag x 2) (bag y 3))) 3))
(check-sat)
