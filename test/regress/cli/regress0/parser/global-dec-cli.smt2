; COMMAND-LINE: --global-declarations -i
; EXPECT: sat
(set-logic ALL)
(push)
(declare-fun x () Int)
(pop)
(assert (> x 0))

(check-sat)
