; DISABLE-TESTER: lfsc
; COMMAND-LINE: --fp-exp
; EXPECT: unsat

(set-logic QF_FP)
(set-info :source |Written by Martin for issue #2932|)
(set-info :smt-lib-version 2.6)
(set-info :category crafted)
(set-info :status unsat)

(declare-fun x () (_ FloatingPoint 3 5))
(assert (fp.isPositive x))

(declare-fun xx () (_ FloatingPoint 3 5))
(assert (= xx (fp.roundToIntegral RNE x)))

(assert (not (= x xx)))

(declare-fun xxx () (_ FloatingPoint 3 5))
(assert (= xxx (fp.roundToIntegral RNE xx)))

(assert (not (= xx xxx)))

(check-sat)
(exit)
