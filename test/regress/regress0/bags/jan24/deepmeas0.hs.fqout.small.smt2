(set-logic ALL)
(set-info :status unsat)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun S () (Bag Int))
(declare-fun T () (Bag Int))

(assert (>= (bag.count x S) 1))

(assert (= S (bag.union_disjoint T (bag y 1))))

(assert (not (= x y)))

(assert (not (>= (bag.count x T) 1)))

(check-sat)
