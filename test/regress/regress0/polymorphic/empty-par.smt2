; COMMAND-LINE: --quant-polymorphic
; EXPECT: unsat
(set-logic QF_LIA)
(assert (par () (= 4 5)))
(check-sat)
