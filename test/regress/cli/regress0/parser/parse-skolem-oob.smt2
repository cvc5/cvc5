; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Not enough indices for skolem operator"
; EXPECT: Not enough indices for skolem operator
; EXIT: 1
(set-option :parse-skolem-definitions true)
(set-logic ALL)
(declare-sort S 0)
(declare-const a (Array S S))
(assert (= (@array_deq_diff a) a))
(check-sat)
