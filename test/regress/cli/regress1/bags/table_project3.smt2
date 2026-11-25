; REQUIRES: unrestricted-mode
; A projection on no columns, whose proof once crashed RARE reconstruction
; CPC checking fails because the signature does not define table.project.
; DISABLE-TESTER: cpc
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Table Int String))
(assert (bag.member (tuple 1 "a") A))
(assert (not (bag.member tuple.unit (table.project A))))
(check-sat)
