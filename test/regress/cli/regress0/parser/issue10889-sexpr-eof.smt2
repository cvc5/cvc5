; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Expected SMT-LIBv2 s-expression"
; EXPECT: Expected SMT-LIBv2 s-expression
; EXIT: 1
(set-logic ALL)
(set-option :incremental (true
(declare-const i2 Int)
(push 1)
(assert (>= i2 -1))
(check-sat)
