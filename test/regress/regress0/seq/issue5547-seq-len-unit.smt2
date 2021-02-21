; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun seq3 () (Seq Int))
(declare-fun seq10 () (Seq Int))
(declare-fun seq12 () (Seq Int))
(assert (seq.suffixof (seq.++ (seq.unit (seq.len (seq.++ seq12 (seq.rev seq3)))) seq3) seq10))
(check-sat)
