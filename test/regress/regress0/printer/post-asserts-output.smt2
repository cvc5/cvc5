; COMMAND-LINE: -o post-asserts --produce-assertions
; SCRUBBER: grep -E '\(assert'
; EXPECT: (assert true)
; EXPECT: (assert true)
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
