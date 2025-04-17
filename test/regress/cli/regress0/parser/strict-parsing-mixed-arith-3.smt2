; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --strict-parsing
; SCRUBBER: grep -o "Subexpressions must have the same type"
; EXPECT: Subexpressions must have the same type
; EXIT: 1
(set-logic ALL)
(assert (= 0 0.0))
(check-sat)
