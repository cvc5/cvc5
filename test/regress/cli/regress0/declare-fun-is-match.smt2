; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic HO_UFIDL)
(set-info :status sat)
(declare-fun _match (Int Int) Int)
(declare-fun is (Int Int) Int)
(assert (= _match is))
(check-sat)
(exit)
