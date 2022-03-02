; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun st5 () (Set Int))
(declare-fun st6 () (Set Int))
(declare-fun st11 () (Set Int))
(assert (or (set.is_singleton (set.complement st6)) (>= 10 (set.card st11) 65 0 0)))
(assert (set.is_singleton st5))
(check-sat)
