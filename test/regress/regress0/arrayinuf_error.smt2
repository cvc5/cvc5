; EXPECT-ERROR: (error "Parse Error: arrayinuf_error.smt2:3.21: Symbol 'Array' not declared as a type")
(set-logic QF_UF)
(declare-fun a (Array Bool Bool))
; EXIT: 1
