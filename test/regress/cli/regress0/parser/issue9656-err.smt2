; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(declare-const f (Int Int) Int)
(check-sat)
(exit)
