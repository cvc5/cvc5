; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-const a Real)
(declare-const b Real)
(assert (> (arccos a) (arccos b)))
(check-sat)
