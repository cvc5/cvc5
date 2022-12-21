; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Symbol 'Array' not declared as a type"
; EXPECT: Symbol 'Array' not declared as a type
(set-logic QF_UF)
(declare-fun a (Array Bool Bool))
; EXIT: 1
