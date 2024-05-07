; COMMAND-LINE: --foreign-theory-rewrite
; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (or
(< (str.len s) 0)
(= (str.len (str.++ "ABC" s)) 1)
(not (>= (str.len s) 0))))
(check-sat)
