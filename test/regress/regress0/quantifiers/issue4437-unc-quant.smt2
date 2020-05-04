; EXPECT: (error "The logic was specified as QF_AUFBVLIA, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
; EXPECT: The fact:
; EXPECT: (forall ((c (_ BitVec 8))) (= (bvashr c a) b) )")
; EXIT: 1
(set-logic QF_AUFBVLIA)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (forall ((c (_ BitVec 8))) (= (bvashr c a) b)))
(check-sat)
