; COMMAND-LINE: --timeout-core-timeout=200 --print-cores-full
; REQUIRES: no-competition
; EXPECT: sat
; EXPECT: unsat
; EXPECT: (
; EXPECT: (not A)
; EXPECT: )
(set-logic ALL)
(set-option :produce-unsat-cores true)
(get-timeout-core-assuming
 (
 true
 )
)
(declare-const A Bool)
(assert A)
(get-timeout-core-assuming
 (
 (not A)
 )
)
