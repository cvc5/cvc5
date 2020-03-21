; EXPECT: sat
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in.re a (re.++ (str.to.re b) (re.* re.allchar))))
(check-sat)
