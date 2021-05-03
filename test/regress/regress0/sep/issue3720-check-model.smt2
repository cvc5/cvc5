; COMMAND-LINE: --quiet
; EXPECT: sat
(set-logic ALL)
(declare-heap (Int Int))
(assert (_ emp Int Int))
(check-sat)
