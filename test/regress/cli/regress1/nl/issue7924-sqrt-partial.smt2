; COMMAND-LINE: --arith-no-partial-fun -q
; EXPECT: sat
(set-logic ALL)
(assert (exists ((V Real)) (distinct (sqrt 1.0) (sqrt 0.0))))
(check-sat)
