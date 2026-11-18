; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Overloaded constants must be type cast."
; EXPECT: Overloaded constants must be type cast.
; EXIT: 1
(set-logic ALL)
(declare-const true Int)
(assert (or true false false))
(check-sat)
