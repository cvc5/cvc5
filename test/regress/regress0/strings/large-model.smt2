; COMMAND-LINE: --lang=smt2.6 --check-models
; EXPECT: (error "The model was computed to have strings of length 100000000000000000000000000000000000000000000000001. We only allow strings up to length 4294967295")
; EXIT: 1
(set-logic SLIA)
(declare-fun x () String)
(assert (> (str.len x) 100000000000000000000000000000000000000000000000000))
(check-sat)
