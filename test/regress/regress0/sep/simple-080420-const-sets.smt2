; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun x () Int)

; works
;(assert (sep (pto 1 2) (pto 5 6) (pto x 8)))

; didn't work due to sets rewriter
(assert (sep (pto 1 2) (pto 5 6) (pto 7 8)))

(check-sat)
