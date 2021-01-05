; COMMAND-LINE: --str-len-simplify -q
; EXPECT: sat
(set-logic ALL)
(assert (forall ((x (Seq Int)) ) (>= (seq.len x) 0)))
(check-sat)
