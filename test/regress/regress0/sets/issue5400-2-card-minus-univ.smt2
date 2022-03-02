(declare-fun s () (Set Int))
(assert (or (set.is_singleton (set.complement s)) (and (= 0 (set.card s)) (= 1 (set.card s)))))
(check-sat)
