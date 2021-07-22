; COMMAND-LINE: --foreign-theory-rewrite -q
; EXPECT: sat
(set-logic ALL)
(assert (forall ((x (Seq Int)) ) (>= (seq.len x) 0)))
(check-sat)
