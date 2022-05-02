; This test checks the correct output behavior of SMT-LIBv2 symbols
; (sometimes they have to be |quoted| with pipes).
;
; COMMAND-LINE: -qm
(declare-fun |toto| () Bool)
(declare-fun |to to| () Bool)
(assert (and toto |to to|))
(check-sat)
; EXPECT: sat
(get-model)
; EXPECT: (
; EXPECT: (define-fun toto () Bool true)
; EXPECT: (define-fun |to to| () Bool true)
; EXPECT: )
