; COMMAND-LINE: --strings-exp --str-len-simplify
; EXPECT: sat
(set-logic ALL)
(assert (forall ((x (Seq Int)) ) (>= (seq.len x) 0)))
(check-sat)
