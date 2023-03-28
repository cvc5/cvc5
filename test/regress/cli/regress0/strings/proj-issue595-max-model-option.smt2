; COMMAND-LINE: -q
; EXPECT: (error "Error in option parsing: strings-model-max-len = 8684616718623666369 is not a legal setting, value should be at most 2147483647.")
; EXPECT: sat
(set-logic ALL)
(set-option :strings-model-max-len 8684616718623666369)
(declare-const x String)
(assert (str.is_digit (str.at x 770055295728)))
(check-sat)
