; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort E 0)
(declare-fun k () E)
(declare-fun s () (Seq E))
(declare-fun j () Int)
(assert (distinct (distinct s (str.update s j (seq.unit (seq.nth s 1)))) (distinct s (str.update (str.update s 0 (seq.unit k)) j (seq.unit (seq.nth s 1))))))
(check-sat)
