; COMMAND-LINE: --seq-array=lazy --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun v () (Seq Int))
(assert (= 1 (seq.len v)))
(assert (= v (seq.update v 0 (seq.unit 1))))
(check-sat)
