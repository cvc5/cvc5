; SCRUBBER: sed -e 's/Bool.*$/Bool/'
; COMMAND-LINE: --dump-models
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun v16 () Bool
; EXPECT: )
(set-logic UFLIA)
(declare-fun v16 () Bool)
(check-sat)
