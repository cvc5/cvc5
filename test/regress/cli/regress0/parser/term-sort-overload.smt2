; COMMAND-LINE: --no-term-sort-overload
; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot bind U to symbol"
; EXPECT: Cannot bind U to symbol
; EXIT: 1
(set-logic ALL)
(declare-sort U 0)
(declare-fun U (Int) Int)
(check-sat)
