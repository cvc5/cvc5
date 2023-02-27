; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT: doesn't include THEORY_QUANTIFIERS
; SCRUBBER: grep -o "doesn't include THEORY_QUANTIFIERS"
; EXIT: 1
(set-logic QF_AUFBVLIA)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (forall ((c (_ BitVec 8))) (= (bvashr c a) b)))
(check-sat)
