(set-logic ALL)
(set-info :status unsat)

(declare-fun S () (Bag Int))
(declare-fun x () Int)

(assert (>= (bag.count (+ 5 x) S) 1))
(assert (not (>= (bag.count 9 S) 1)))
(assert (= x 4))

(check-sat)
