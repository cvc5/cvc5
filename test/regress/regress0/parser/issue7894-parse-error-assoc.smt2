; DISABLE-TESTER: dump
; SCRUBBER: grep -o "must have at least 2 children"
; EXPECT: must have at least 2 children
; EXIT: 1
(assert (= (+ 0)))
