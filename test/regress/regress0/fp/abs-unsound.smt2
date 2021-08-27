; COMMAND-LINE: --fp-exp
; EXPECT: sat
(set-logic QF_FP)
(set-info :status sat)
(declare-fun x () (_ FloatingPoint 3 5))
(declare-fun y () (_ FloatingPoint 3 5))

(assert (not (= (fp.abs (fp.abs x)) x)))
(assert (not (= (fp.abs (fp.neg y)) y)))

(check-sat)
