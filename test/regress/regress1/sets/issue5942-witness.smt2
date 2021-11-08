; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun r1 () Real)
(declare-fun st9 () (Set String))
(declare-fun str2 () String)
(assert (set.is_singleton (ite (= str2 (str.substr str2 0 (to_int r1))) st9 (as set.empty (Set String)))))
(check-sat)
