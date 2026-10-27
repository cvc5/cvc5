; REQUIRES: no-competition
; EXPECT: (error "Parse Error: issue10093.smt2:7.44: expecting a string-like term in argument of str.prefixof")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-fun a () String)
(assert (str.prefixof (str.substr a 0 10) 2))
(check-sat)
