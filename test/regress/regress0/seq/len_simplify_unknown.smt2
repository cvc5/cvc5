; COMMAND-LINE: -q
; EXPECT: unknown
(set-logic ALL)
(assert (forall ((x (Seq Int)) ) (>= (seq.len x) 0)))
(check-sat)
