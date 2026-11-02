; REQUIRES: unrestricted-mode
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun A () (Bag Int))
(declare-fun S () (Bag (Bag Int)))
(assert (>= (bag.count (bag.map f A) S) 1))
(assert (>= (bag.count 5 (bag.map f A)) 1))
(check-sat)
