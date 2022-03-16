; EXPECT: sat
; COMMAND-LINE: --sygus-inference -q
(set-logic LIA)
(assert (forall ((a Int)) (=> (> a 0) (exists ((b Int)) (> a (* b 2))))))
(check-sat)
