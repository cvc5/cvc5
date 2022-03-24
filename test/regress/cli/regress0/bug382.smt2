; EXPECT: sat
; EXPECT: ((x 0))
; EXPECT: ((x 0))
; EXPECT: (((f x) 0))
; EXPECT: (((f x) 0))
(set-option :produce-models true)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(check-sat)
(get-value (x)); returns 0
(get-value (x)); returns 1 ?!
(get-value ((f x))); assert-fails in EqualityEngine
(get-value ((f x)))
