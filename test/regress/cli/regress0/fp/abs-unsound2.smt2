; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic QF_FP)
(set-info :status unsat)
(declare-fun x () (_ FloatingPoint 3 5))

(assert (fp.isNegative (fp.abs (fp.neg x))))

(check-sat)
