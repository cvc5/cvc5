; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-heap (Int Int))
(declare-fun x () Int)

; works
;(assert (sep (pto 1 2) (pto 5 6) (pto x 8)))

; didn't work due to sets rewriter
(assert (sep (pto 1 2) (pto 5 6) (pto 7 8)))

(check-sat)
