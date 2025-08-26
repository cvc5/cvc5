; EXIT: 1
; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
(set-logic ALL)
(assert (nullable.some))
(check-sat)
