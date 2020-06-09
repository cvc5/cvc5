; COMMAND-LINE: --quiet
; EXPECT: sat
(set-logic ALL)
(assert (_ emp Int Int))
(check-sat)
