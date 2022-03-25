; EXPECT: sat
; COMMAND-LINE: --sygus-inference --quiet
(set-logic HO_ALL)
(declare-fun f (Int) Bool)
(declare-fun g (Int) Bool)
(assert (and (distinct f g) (g 0)))
(assert (exists ((x Int)) (f x)))
(check-sat)
