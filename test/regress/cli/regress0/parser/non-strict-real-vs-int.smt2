; COMMAND-LINE: --no-strict-parsing
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Real)
(assert (= x 10))
(check-sat)
