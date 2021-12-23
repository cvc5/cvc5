; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Bag Int))
(assert (bag.is_singleton (set.complement (set.complement S))))
(assert (= 2 (bag.card S)))
(check-sat)