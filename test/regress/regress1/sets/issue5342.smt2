; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Set Int))
(assert (is_singleton (complement (complement S))))
(assert (= 2 (card S)))
(check-sat)