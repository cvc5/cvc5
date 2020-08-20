; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun z () (Seq Int))
(declare-fun i () Int)
(declare-fun n () Int)
(assert (= (seq.extract z n 1) (seq.unit i)))
(assert (< (seq.len z) n))
(check-sat)
