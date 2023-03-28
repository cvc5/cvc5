; EXPECT: (error "Error in option parsing: global negate not supported in sygus.")
; EXIT: 1
(set-logic ALL)
(set-option :global-negate true)
(set-option :produce-interpolants true)
(declare-fun x () Bool)
(get-interpolant A x)
