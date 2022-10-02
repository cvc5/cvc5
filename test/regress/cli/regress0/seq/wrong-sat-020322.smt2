; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-sort E 0)
(declare-fun k () E)
(declare-fun s () (Seq E))
(assert (distinct
                (distinct s (str.update s 0 (seq.unit (seq.nth s 0))))
                (distinct s
                               (str.update (str.update s 0 (seq.unit k))
                                                   0
                                                   (seq.unit (seq.nth s 0))))))
(check-sat)
