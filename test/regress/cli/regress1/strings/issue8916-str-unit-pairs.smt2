; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: sat
(set-logic ALL)
(declare-fun v () String)
(assert (exists ((E String)) (or (>= (+ 1 (str.to_int (str.at v 0))) 10))))
(assert (forall ((E String)) (<= (str.to_int v) 0)))
(check-sat)
