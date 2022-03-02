; EXPECT: (error "Term of kind real.pi requires nl-ext mode to be set to value 'full'")
; EXIT: 1
(set-logic ALL)
(set-option :nl-ext light)
(assert (< real.pi 0.0))
(check-sat)
