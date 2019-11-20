; REQUIRES: proof
; COMMAND-LINE: --incremental --proof
; EXPECT: (error "Error in option parsing: --incremental is not supported with proofs")
; EXIT: 1
(set-logic QF_BV)
(check-sat)
