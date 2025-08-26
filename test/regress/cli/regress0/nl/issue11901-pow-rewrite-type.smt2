; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(assert (distinct 0 (^ 0 4.0))) 
(check-sat)
