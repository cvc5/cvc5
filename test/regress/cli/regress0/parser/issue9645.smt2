; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Unexpected number of numerals for +zero"
; EXPECT: Unexpected number of numerals for +zero
; EXIT: 1
(set-logic ALL)
(assert (= (_ +zero 5unsigned)))
