; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun z () (Seq Int))
(declare-fun i () Int)
(declare-fun n () Int)
(assert (> i 777))
(assert (= (seq.extract z n 1) (seq.unit i)))
(check-sat)
