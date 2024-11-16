; EXIT: 1
; EXPECT: (error "Parse Error: test.smt2:2.23: nullable.some requires exactly one argument.")
(set-logic ALL)
(assert (nullable.some))
(check-sat)
