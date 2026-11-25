; REQUIRES: unrestricted-mode
; A grouping on no columns, whose proof once crashed RARE reconstruction and
; the CPC printer
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Table Int String))
(assert (bag.member (tuple 1 "a") A))
(assert (= (table.group A) (as bag.empty (Bag (Table Int String)))))
(check-sat)
