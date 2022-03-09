; COMMAND-LINE: -o pre-asserts
; SCRUBBER: grep -E '\(assert'
; EXPECT: (assert (= x x))
; EXPECT: (assert true)
(set-logic ALL)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
