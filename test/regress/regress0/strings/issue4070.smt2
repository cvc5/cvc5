; EXPECT: sat
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re a (re.++ (str.to_re b) (re.* re.allchar))))
(check-sat)
