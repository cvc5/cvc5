; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-const a Real)
(assert (<= (- 1.1) a 1.0))
(assert (< (arccos a) 0.0))
(check-sat)
