; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
; the union max of two constructed bags is (bag x 3) when x and y are equal,
; of cardinality 3, and a bag of cardinality 2 + 3 otherwise, so 4 is not a
; possible cardinality. This needs the count of each constructed bag to be
; concentrated on one element.
(assert (= (bag.card (bag.union_max (bag x 2) (bag y 3))) 4))
(check-sat)
