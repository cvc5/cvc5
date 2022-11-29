; EXPECT: sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(assert (= true (fp.eq x ((_ to_fp 11 53) (_ bv13831004815617530266 64))) true))
(set-info :status sat)
(check-sat)
