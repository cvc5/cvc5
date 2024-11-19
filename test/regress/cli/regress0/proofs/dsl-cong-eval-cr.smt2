; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun  x1 () String )
(declare-fun  x2 () String )
(declare-fun  z () String )
(declare-fun  t1 () String )
(declare-fun  t2 () String )
(assert (= (str.++ (str.++ (str.++ "abc" z) (str.++ (str.++ x1 "abvv") x2)) t2) (str.++ (str.++ z "vba") (str.++ (str.++ (str.++ x2 "dcba") x1) t1))))
(check-sat)
