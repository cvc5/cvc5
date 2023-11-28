; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic HO_ALL)
(set-option :sygus-fair direct)
(declare-datatypes ((d 0)) (((c))))
(define-fun f ((_f46_0 d)) d _f46_0)
(find-synth :rewrite_input)
