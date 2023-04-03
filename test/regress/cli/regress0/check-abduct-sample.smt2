; COMMAND-LINE: -q
; SCRUBBER: sed -e 's/(define-fun.*/(define-fun/'
; EXPECT: (define-fun
(set-option :cegis-sample trust)
(set-option :produce-abducts true)
(set-option :check-abducts true)
(declare-const x Bool)
(get-abduct A x)
