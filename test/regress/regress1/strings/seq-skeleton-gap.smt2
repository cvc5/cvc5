; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Seq Int))
(assert (< 1 (seq.len (seq.update a 0 (seq.unit 1)))))
(assert (distinct a (seq.update a 0 (seq.unit 1))))
(check-sat)
