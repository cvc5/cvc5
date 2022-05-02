; EXPECT: sat
(set-logic QF_FP)
(declare-fun a () RoundingMode)
(declare-fun b () (_ FloatingPoint 8 24))
(assert (= b (fp.add a b (fp.add a ((_ to_fp 8 24) a ((_ to_fp 8 24) a 0.0)) b))))
(check-sat)
