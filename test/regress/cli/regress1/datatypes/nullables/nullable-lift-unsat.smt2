; DISABLE-TESTER: lfsc
; DISABLE-TESTER: cpc
(set-logic HO_ALL)
(set-info :status unsat)
(assert (= (nullable.lift (lambda ((x Bool) (y Bool)) (and x y)) (nullable.some false) (nullable.some false)) (nullable.some true)))
(check-sat)
