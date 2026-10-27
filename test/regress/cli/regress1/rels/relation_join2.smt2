; REQUIRES: unrestricted-mode
; CPC checking fails because the signature does not define rel.table_join.
; DISABLE-TESTER: cpc
(set-logic HO_ALL)
(set-info :status unsat)
(assert (set.member (tuple 1 2 1 9)
  ((_ rel.table_join 0 0 1 0)
    (set.singleton (tuple 1 2))
    (set.singleton (tuple 1 9)))))
(check-sat)
