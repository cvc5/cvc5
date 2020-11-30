; REQUIRES: symfpu
(set-logic QF_FPLRA)
(set-info :status sat)
(declare-fun a () (_ FloatingPoint 11 53))
(assert (= (fp.to_real a) 0.0))
(check-sat)

