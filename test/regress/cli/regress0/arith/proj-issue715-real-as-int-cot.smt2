; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(set-option :solve-real-as-int true)
(declare-const x Real)
(assert (is_int (cot x)))
(push)
(check-sat)
