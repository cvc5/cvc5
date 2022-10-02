; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Set Int))
(declare-fun P ((Set Int)) Bool)

(assert (P x))
(assert (not (P (set.singleton 0))))
(assert (set.member 1 x))
(assert (not (set.member 0 (as set.universe (Set Int)))))

(check-sat)
