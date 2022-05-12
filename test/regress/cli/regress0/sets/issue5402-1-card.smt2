; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(declare-fun s () (Set Int))
(assert (set.is_singleton (set.complement (set.singleton 0))))
(assert (= 2 (set.card s)))
(check-sat)
