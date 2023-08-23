(set-logic HO_ALL)
(set-info :status sat)
(declare-fun f (Int) Int)

(declare-fun S () (Set Int))
(declare-fun x () Int)

(assert (not (set.member x S)))
(assert (set.member (f x) (set.map f S)))

(check-sat)
