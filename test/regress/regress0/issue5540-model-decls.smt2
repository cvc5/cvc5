; SCRUBBER: sed -e 's/Bool.*$/Bool/'
; COMMAND-LINE: --dump-models -i
; EXPECT:sat
; EXPECT: (
; EXPECT: (define-fun a () Bool
; EXPECT: )
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun a () Bool
; EXPECT: )
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun a () Bool
; EXPECT: )
(set-logic ALL)
(declare-fun a () Bool)
(check-sat)
(check-sat)
(check-sat)
