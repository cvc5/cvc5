(set-logic ALL)
(set-info :status unsat)

(declare-fun S () (Set Int))
(declare-fun x () Int)

(assert (set.member (+ 5 x) S))
(assert (not (set.member 9 S)))
(assert (= x 4))

(check-sat)
