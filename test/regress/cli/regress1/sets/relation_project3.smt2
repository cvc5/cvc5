; REQUIRES: unrestricted-mode
; A projection on no columns, whose proof once crashed RARE reconstruction
; CPC checking fails because the signature does not define rel.project.
; DISABLE-TESTER: cpc
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun R () (Relation Int String))
(assert (set.member (tuple 1 "a") R))
(assert (not (set.member tuple.unit (rel.project R))))
(check-sat)
