; COMMAND-LINE: --bvand-integer-granularity=9
; EXPECT: Error in option parsing
; SCRUBBER: grep -o "Error in option parsing"
; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXIT: 1
(set-logic QF_NIA)
(check-sat)
