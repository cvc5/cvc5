; REQUIRES: no-competition
; EXPECT: Quantifier used in non-quantified logic
; SCRUBBER: grep -o "Quantifier used in non-quantified logic"
; EXIT: 1
(set-logic QF_AUFBVLIA)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (forall ((c (_ BitVec 8))) (= (bvashr c a) b)))
(check-sat)
