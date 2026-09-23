; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
; the intersection of two constructed bags is (bag x 1) when x and y are
; equal and the empty bag otherwise, so its cardinality is 0 or 1
(assert (= (bag.card (bag.inter_min (bag x 3) (bag y 1))) 2))
(check-sat)
