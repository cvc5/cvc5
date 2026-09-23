; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
; the cardinality of the union max of two disjoint constructed bags is 2 + 3
(assert (not (= x y)))
(assert (= (bag.card (bag.union_max (bag x 2) (bag y 3))) 5))
(check-sat)
