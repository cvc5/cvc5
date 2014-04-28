; EXPECT-ERROR: (error "Parse Error: arrayinuf_error.smt2:7.21: Symbol 'Array' not declared as a type
; EXPECT-ERROR: 
; EXPECT-ERROR:   (declare-fun a (Array Bool Bool))
; EXPECT-ERROR:                   ^
; EXPECT-ERROR: ")
(set-logic QF_UF)
(declare-fun a (Array Bool Bool))
; EXIT: 1
