; COMMAND-LINE: -o pre-asserts
; SCRUBBER: grep -E '\(assert'
; EXPECT: (assert (= x x))
(set-logic ALL)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
