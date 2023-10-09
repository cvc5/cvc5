; EXPECT: (error "Parse Error: ./regress0/parser/issue10093.smt2:5.44: expecting a string-like term in argument of str.prefixof")
; EXIT: 1
(set-logic ALL)
(declare-fun a () String)
(assert (str.prefixof (str.substr a 0 10) 2))
(check-sat)
