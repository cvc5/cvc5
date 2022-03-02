; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun s () (Set Int))
(assert (or (set.is_singleton (set.complement s)) (and (= 0 (set.card s)) (= 1 (set.card s)))))
(check-sat)
