; SCRUBBER: grep -v -E '.*'
; EXIT: 1
(set-logic HO_ALL)
(set-option :sygus-fair direct)
(set-option :sygus-rr-synth-input true)
(declare-datatypes ((d 0)) (((c))))
(define-fun f ((_f46_0 d)) d _f46_0)
(check-sat)
