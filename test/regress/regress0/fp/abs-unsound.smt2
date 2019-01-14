(set-logic QF_FP)
(set-info :status sat)
(declare-fun x () (_ FloatingPoint 3 5))

(assert (not (= (fp.abs (fp.abs x)) x)))

(check-sat)
