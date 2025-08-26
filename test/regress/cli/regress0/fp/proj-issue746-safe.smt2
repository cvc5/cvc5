; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot handle term with type"
; EXPECT: Cannot handle term with type
; EXIT: 1
(set-option :safe-mode safe)
(set-logic ALL)
(declare-const x RoundingMode)
(declare-const x6 RoundingMode)
(assert (= x6 x))
(check-sat)
