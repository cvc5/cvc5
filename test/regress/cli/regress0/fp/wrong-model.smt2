; COMMAND-LINE: --fp-exp
; EXPECT: sat

; NOTE: the (set-logic ALL) is on purpose because the problem was not triggered
; with QF_FP.
(set-logic ALL)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(assert (not (= (fp.isSubnormal x) false)))
(check-sat)
