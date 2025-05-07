; COMMAND-LINE: --bvand-integer-granularity=9
; EXPECT-ERROR: Error in option parsing
; ERROR-SCRUBBER: grep -o "Error in option parsing"
; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXIT: 1
(set-logic QF_NIA)
(check-sat)
