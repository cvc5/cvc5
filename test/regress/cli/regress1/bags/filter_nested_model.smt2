; REQUIRES: unrestricted-mode
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun p (Int) Bool)
(declare-fun A () (Bag Int))
(declare-fun S () (Bag (Bag Int)))
(assert (>= (bag.count (bag.filter p A) S) 1))
(assert (>= (bag.count 5 (bag.filter p A)) 1))
(check-sat)
