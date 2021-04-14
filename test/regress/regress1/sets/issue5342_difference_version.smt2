; COMMAND-LINE: --sets-ext
(set-logic ALL)
(set-info :status unsat)
(declare-fun S () (Set Int))
(assert (is_singleton (setminus (as univset (Set Int)) (setminus (as univset (Set Int)) S))))
(assert (= 2 (card S)))
(check-sat)