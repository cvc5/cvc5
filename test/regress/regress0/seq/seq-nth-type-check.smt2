; DISABLE-TESTER: dump
; EXPECT: expecting a sequence
; SCRUBBER: grep -o "expecting a sequence"
; EXIT: 1
(set-logic QF_SLIA)
(declare-const i Int)
(assert (= i (seq.nth 0 i)))
(check-sat)
