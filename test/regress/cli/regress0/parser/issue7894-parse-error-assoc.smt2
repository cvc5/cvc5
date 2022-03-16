; DISABLE-TESTER: dump
; COMMAND-LINE: -q
; SCRUBBER: grep -o "must have at least 2 children"
; EXPECT: must have at least 2 children
; EXIT: 1
(assert (= (+ 0)))
