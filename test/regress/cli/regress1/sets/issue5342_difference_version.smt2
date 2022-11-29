; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Set Int))
(assert (set.is_singleton (set.minus (as set.universe (Set Int)) (set.minus (as set.universe (Set Int)) S))))
(assert (= 2 (set.card S)))
(check-sat)