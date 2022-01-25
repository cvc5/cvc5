; COMMAND-LINE: -o post-asserts --produce-assertions
; SCRUBBER: sed -e 's/;.*//'
; EXPECT: (set-logic ALL)
; EXPECT: (assert true)
; EXPECT: (assert true)
; EXPECT: (check-sat)
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
