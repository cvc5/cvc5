; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Expected non-empty list of terms for get-value"
; EXPECT: Expected non-empty list of terms for get-value
; EXIT: 1
(set-logic ALL)
(get-value ())
