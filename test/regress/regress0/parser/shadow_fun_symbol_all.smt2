; DISABLE-TESTER: dump
; EXPECT: Symbol `sin' is shadowing a theory function symbol
; SCRUBBER: grep -o "Symbol \`sin' is shadowing a theory function symbol"
; EXIT: 1
(set-logic ALL)
(declare-fun sin (Real) Real)
