; COMMAND-LINE: --lang=smt2.6 --check-models
; EXPECT: (error "Cannot generate model with string whose length exceeds UINT32_MAX")
; EXIT: 1
(set-logic SLIA)
(declare-fun x () String)
(assert (> (str.len x) 100000000000000000000000000000000000000000000000000))
(check-sat)
