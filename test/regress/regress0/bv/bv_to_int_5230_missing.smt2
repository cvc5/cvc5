; EXPECT: sat
(set-logic BV)
(set-option :solve-bv-as-int sum)
(assert (exists ((q4 (_ BitVec 6))) true))
(check-sat)
