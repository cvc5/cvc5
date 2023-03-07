; DISABLE-TESTER: dump
; EXPECT: expecting a string-like
; SCRUBBER: grep -o "expecting a string-like"
; EXIT: 1
(set-logic QF_SLIA)
(declare-const i Int)
(assert (= i (seq.nth 0 i)))
(check-sat)
