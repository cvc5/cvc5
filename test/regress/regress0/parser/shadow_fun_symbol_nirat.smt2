; DISABLE-TESTER: dump
; EXPECT: Symbol `exp' is shadowing a theory function symbol
; SCRUBBER: grep -o "Symbol \`exp' is shadowing a theory function symbol"
; EXIT: 1
(set-logic NIRAT)
(declare-fun exp (Real) Real)
