; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic NIA)
(declare-fun i3 () Int)
(declare-fun i9 () Int)
(push)
(assert (>= (- 1 1 i3 i9 1) i3))
(check-sat)
(pop)
(assert (or (= 0 i9) (< i3 0)))
(assert (= 1 (* i9 i9)))
(check-sat)
