; EXPECT: sat
(set-logic ABV)
(set-option :check-unsat-cores true)
(set-option :solve-bv-as-int sum)
(assert (! (exists ((q4 (_ BitVec 6))) true) :named IP_2))
(check-sat)
