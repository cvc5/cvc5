; REQUIRES: no-restricted-mode
(set-logic ALL)
(set-info :status sat)
(declare-fun B () (Bag String))
(assert (bag.member "x" B))
(check-sat)
