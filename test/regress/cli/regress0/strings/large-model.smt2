; COMMAND-LINE: -q
; EXPECT: sat
(set-logic SLIA)
(declare-fun x () String)
(assert (> (str.len x) 100000000000000000000000000000000000000000000000000))
(check-sat)
