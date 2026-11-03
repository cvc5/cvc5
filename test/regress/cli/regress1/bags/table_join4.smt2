; REQUIRES: unrestricted-mode
; CPC checking fails because the signature does not define table.join.
; DISABLE-TESTER: cpc
(set-logic HO_ALL)
(set-info :status unsat)
(assert (bag.member (tuple 1 2 1 9)
  ((_ table.join 0 0 1 0)
    (bag (tuple 1 2) 1)
    (bag (tuple 1 9) 1))))
(check-sat)
