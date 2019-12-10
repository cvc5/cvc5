; EXPECT: sat
; COMMAND-LINE: --uf-ho
(set-info :smt-lib-version 2.6)
(set-logic UFIDL)
(set-info :status sat)
(declare-fun match (Int Int) Int)
(declare-fun is (Int Int) Int)
(assert (= match is))
(check-sat)
(exit)
