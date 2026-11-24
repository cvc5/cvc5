; REQUIRES: unrestricted-mode
; The columns of (table.product A B) are those of A, then those of B, here
; of different sorts
(set-logic ALL)
(set-info :status unsat)
(declare-fun A () (Table Int))
(declare-fun B () (Table String))
(assert (bag.member (tuple 1) A))
(assert (bag.member (tuple "a") B))
(assert (not (bag.member (tuple 1 "a") (table.product A B))))
(check-sat)
