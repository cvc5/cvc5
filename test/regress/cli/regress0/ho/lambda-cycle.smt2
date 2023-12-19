; COMMAND-LINE: --mbqi
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun f (Int Int) Int)
(assert (= f (lambda ((x Int) (y Int)) (f y x))))
(check-sat)
