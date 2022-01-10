; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT: (error "Parse Error: arrayinuf_error.smt2:9.21: Symbol 'Array' not declared as a type
; EXPECT: 
; EXPECT:   (declare-fun a (Array Bool Bool))
; EXPECT:                   ^
; EXPECT: ")
(set-logic QF_UF)
(declare-fun a (Array Bool Bool))
; EXIT: 1
