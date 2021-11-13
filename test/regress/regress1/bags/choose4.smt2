; COMMAND-LINE: --quiet
(set-logic ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun a () Int)
(assert (not (= A (as bag.empty (Bag Int)))))
(assert (> (bag.count 10 A) 0))
(assert (= a (bag.choose A)))
(check-sat)
