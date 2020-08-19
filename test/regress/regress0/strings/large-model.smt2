; COMMAND-LINE: --lang=smt2.6 --check-models
; SCRUBBER: sed -E 's/of length [0-9]+/of length LENGTH/'
; EXPECT: (error "The model was computed to have strings of length LENGTH. We only allow strings up to length 4294967295")
; EXIT: 1
(set-logic SLIA)
(declare-fun x () String)
(assert (> (str.len x) 100000000000000000000000000000000000000000000000000))
(check-sat)
