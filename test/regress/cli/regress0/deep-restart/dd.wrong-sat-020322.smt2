; COMMAND-LINE: --deep-restart=input-and-prop --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-sort E 0)
(declare-fun s () (Seq E))
(assert (distinct s (str.update s 0 (seq.unit (seq.nth s 0)))))
(check-sat)
