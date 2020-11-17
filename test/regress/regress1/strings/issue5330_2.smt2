; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun seq11 () (Seq Int))
(declare-fun i5 () Int)
(declare-fun v17 () Bool)
(declare-fun v24 () Bool)
(assert (xor v17 v24 true true (seq.prefixof (seq.rev (seq.rev seq11)) (seq.unit i5))))
(check-sat)
